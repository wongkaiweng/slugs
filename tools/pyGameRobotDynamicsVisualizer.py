#!/usr/bin/python
#
# Animates a robot according to a continuous-state robot model driven by a slugs synthesized gr(1) controller
#
#
# REQUIREMENTS FOR PROPER Operation:
# - The slugsin file has the state bits in inverse order. This is necessary to solve the problem that Pessoa's abstract are most-significant-bit first
# - There are multiple required files:
#   - PNG file for the workspace
#   - SLUGSIN file for the specification
#   - BDD file for the robot abstraction
#   - COLORCODING file for the simulator options
#   - ROBOTMDL file with model and parameters
#   The files all need to have the same prefix, with the exception of the BDD file, where all things standing behind dots right of the last path separator character ("/") are stripped. This allows
#   recycling the same .bdd file for many scenarios.

# TODO:
# 1. generate png automatically based on x & y propositions in spec
# 2. how to change environment param?
# 3. scaling the png appropriately (max x & y vs. map x & y)
# 4. successively subtract states from each environment safety assumption to eventually get a "minimal" set for each assumption

import math
import os
import sys, code
import resource
import subprocess
import signal
import tempfile
import copy
import itertools
import Image
import os, pygame, pygame.locals
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.image as mpimg
import matplotlib.patches as mpatch

# ==================================
# Settings
# ==================================
MAGNIFY = 64
numMinorIters = 200

# ==================================
# Entry point
# ==================================
if len(sys.argv)<2:
    print >>sys.stderr, "Error: Need PNG file as parameter"
    sys.exit(1)
specFile = sys.argv[1]
bddinfile = sys.argv[2]

# ==================================
# Read input image
# ==================================
import os,sys
pngfile = Image.open(specFile)
pngFileBasis = specFile[0:specFile.rfind(".png")]
# print "Size of Workspace:",pngfile.size
xsizePng = pngfile.size[0]
ysizePng = pngfile.size[1]
imageData = pngfile.getdata()
palette = pngfile.getpalette()
if (xsizePng>1023):
    print >>sys.stderr,"Error: Scenario is too large - not supported."
    sys.exit(1)
if (ysizePng>1023):
    print >>sys.stderr,"Error: Scenario is too large - not supported."
    sys.exit(1)

# ====================================================================
# Read input image color encoding configuration file
# ====================================================================
colorCodingInformationFile = open(pngFileBasis+".colorcoding","r").readlines()
colorCoding = [(int(a.strip().split(" ")[0]),a.strip().split(" ")[1]) for a in colorCodingInformationFile if a.strip()!=""]
colorCodingMap = {a:b for (a,b) in colorCoding}
print colorCoding

# ===================================================================
# Load the robot motion model paramters from file
# ===================================================================
robotmdlfile = pngFileBasis+".robotmdl"
robotModel = open(robotmdlfile,"r")
paramsState = False
cyclicState = False
motionStateOutputState = False
motionControlOutputState = False
systemModelState = False
modelParams = []
cyclicVars = []
motionStateVars = []
motionControlVars = []
systemModel = []
for line in robotModel.readlines():
    line = line.strip()
    if line.startswith("["):
        cyclicState = False
        motionStateOutputState = False
        motionControlOutputState = False
        systemModelState = False
    if line=="[CYCLIC]":
        cyclicState = True
    elif cyclicState and len(line)>0 and not line.startswith("#"):
        cyclicVars.append(line)
    if line=="[MOTION STATE OUTPUT]":
        motionStateOutputState = True
    elif motionStateOutputState and len(line)>0 and not line.startswith("#"):
        motionStateVars.append(line)
    if line=="[MOTION CONTROLLER OUTPUT]":
        motionControlOutputState = True
    elif motionControlOutputState and len(line)>0 and not line.startswith("#"):
        motionControlVars.append(line)
    if line=="[SYSTEM MODEL]":
        systemModelState = True
    elif systemModelState and len(line)>0 and not line.startswith("#"):
        systemModel.append(line)

if len(set(['x','y']).intersection(motionStateVars)) < 2:
    print >> sys.stderr, "x and y must be included as motion state variables in the robot model file"
print motionStateVars
if not all([any([systemModel[j].startswith(motionStateVars[i]) for j in range(len(systemModel))]) for i in range(len(motionStateVars))]):
    print >> sys.stderr, "states and state derivatives don't match in the robot model file"

robotModel = open(robotmdlfile,"r")
motionStateParams = [[[]]*2 for i in range(len(motionStateVars))]
motionControlParams = [[[]]*2 for i in range(len(motionControlVars))]
for line in robotModel.readlines():
    line = line.strip()
    if line.startswith("["):
        paramsState = False
    if line=="[PARAMETERS]":
        paramsState = True
    elif paramsState and len(line)>0 and not line.startswith("#"):
        if line.startswith(('tau','eta','mu')) or line.startswith(tuple(motionStateVars)) or line.startswith(tuple(motionControlVars)):
            modelParams.append(line)
            for i,varName in enumerate(motionStateVars):
                if line.startswith(varName):                  
                    if line.rfind("max") > 0:
                        motionStateParams[i][0] = eval(line[line.rfind("=")+1:])
                    elif line.rfind("min") > 0:
                        motionStateParams[i][1] = eval(line[line.rfind("=")+1:])
                    else:
                        print >> sys.stderr, "min or max state parameter value missing in robot model file"
            for i,varName in enumerate(motionControlVars):
                if line.startswith(varName):
                    if line.rfind("max") > 0:
                        motionControlParams[i][0] = eval(line[line.rfind("=")+1:])
                    elif line.rfind("min") > 0:
                        motionControlParams[i][1] = eval(line[line.rfind("=")+1:])
                    else:
                        print >> sys.stderr, "min or max control parameter value missing in robot model file"
        else:
            print >> sys.stderr, "motion state/control variables don't match parameters in the robot model file"

# evaluate the strings in modelParams
for i in xrange(0,len(modelParams)):
    exec(modelParams[i])
for i,varName in enumerate(motionStateVars):
    while systemModel[i].rfind('sin(') >= 0 and systemModel[i][systemModel[i].rfind('sin(')-3:systemModel[i].rfind('sin(')] != 'np.':
        systemModel[i] = systemModel[i][0:systemModel[i].rfind('sin(')]+'np.'+systemModel[i][systemModel[i].rfind('sin('):]
    while systemModel[i].rfind('cos(') >= 0 and systemModel[i][systemModel[i].rfind('cos(')-3:systemModel[i].rfind('cos(')] != 'np.':
        systemModel[i] = systemModel[i][0:systemModel[i].rfind('cos(')]+'np.'+systemModel[i][systemModel[i].rfind('cos('):]
    while systemModel[i].rfind('tan(') >= 0 and systemModel[i][systemModel[i].rfind('tan(')-3:systemModel[i].rfind('tan(')] != 'np.':
        systemModel[i] = systemModel[i][0:systemModel[i].rfind('tan(')]+'np.'+systemModel[i][systemModel[i].rfind('tan('):]
# maxMotion = [int(np.floor(np.true_divide((motionStateParams[i][0] - motionStateParams[i][1]),eta))) for i in range(len(motionStateParams))] #greatest index
tmp = [[motionStateParams[i][0]+1e-6,motionStateParams[i][1]-1e-6] for i in range(len(motionStateParams))]  #based on 0 having no offset
minMaxState = map(list,zip(*tmp))  # absolute bounds on the continuous states
vect1 = [np.arange(0,minMaxState[0][i]+1e-6,eta) for i in range(len(motionStateParams))]
vect2 = [np.arange(0,minMaxState[1][i]-1e-6,-eta) for i in range(len(motionStateParams))]
stateCent = [sorted(np.concatenate((vect1[i],vect2[i][1:]))) for i in range(len(motionStateParams))]
tmp1 = [[stateCent[i][len(stateCent[i])-1],stateCent[i][0]] for i in range(len(motionStateParams))]  #based on 0 having no offset
minMaxStateCent = map(list,zip(*tmp1))  # bounds on the continuous state centroid
print stateCent
print minMaxState
print minMaxStateCent
# maxCtrl = [int(np.floor(np.true_divide((motionControlParams[i][0] - motionControlParams[i][1]),mu))) for i in range(len(motionControlParams))] #greatest index
tmp = [[motionControlParams[i][0]+1e-6,motionControlParams[i][1]-1e-6] for i in range(len(motionControlParams))]  #based on 0 having no offset
minMaxCtrl = map(list,zip(*tmp))  # absolute bounds on the continuous controls
vect1 = [np.arange(0,minMaxCtrl[0][i]+1e-6,mu) for i in range(len(motionControlParams))]
vect2 = [np.arange(0,minMaxCtrl[1][i]-1e-6,-mu) for i in range(len(motionControlParams))]
ctrlCent = [sorted(np.concatenate((vect1[i],vect2[i][1:]))) for i in range(len(motionControlParams))]
tmp1 = [[ctrlCent[i][len(ctrlCent[i])-1],ctrlCent[i][0]] for i in range(len(motionControlParams))]  #based on 0 having no offset
minMaxCtrlCent = map(list,zip(*tmp1))  # bounds on the continuous state centroid
print ctrlCent
print minMaxCtrl
print minMaxCtrlCent

xsize = int((xmax - xmin)/eta)+1
ysize = int((ymax - ymin)/eta)+1
print 'xsize,ysize: ', xsize, ysize
print 'xsizePng,ysizePng: ', xsizePng, ysizePng

# Adapt size of display
pygame.init()
displayInfo = pygame.display.Info()
MAGNIFY = min(MAGNIFY,displayInfo.current_w*3/4/xsizePng)
MAGNIFY = min(MAGNIFY,displayInfo.current_h*3/4/ysizePng)

# ====================================================================
# Read motion state outputs from the input file
# ====================================================================
slugsinfile = pngFileBasis+".slugsin"
slugsReader = open(slugsinfile,"r")
motionStateOutputState = False
motionControlOutputState = False
xMotionStateVars = []
yMotionStateVars = []
motionStateBitVars = [[]]*len(motionStateVars)
motionControlBitVars = [[]]*len(motionControlVars)
for line in slugsReader.readlines():
    line = line.strip()
    if line.startswith("["):
        motionStateOutputState = False
        motionControlOutputState = False
    if line=="[MOTION STATE OUTPUT]":
        motionStateOutputState = True
    elif motionStateOutputState and len(line)>0 and not line.startswith("#"):
        if not line.startswith(tuple(motionStateVars)):
            print >> sys.stderr, line+" not included among motion state variables in the robot model file"
        else:
            for i,varName in enumerate(motionStateVars):
                if line.startswith(varName):
                    k = i
                    if len(motionStateBitVars[k])==0:
                        tmp = []
        tmp.append(line)
        motionStateBitVars[k] = tmp
    if line=="[MOTION CONTROLLER OUTPUT]":
        motionControlOutputState = True
    elif motionControlOutputState and len(line)>0 and not line.startswith("#"):
        if not line.startswith(tuple(motionControlVars)):
            print >> sys.stderr, line+" not included among motion control variables in the robot model file"
        else:
            for i,varName in enumerate(motionControlVars):
                if line.startswith(varName):
                    k = i
                    if len(motionControlBitVars[k])==0:
                        tmp = []
        tmp.append(line)
        motionControlBitVars[k] = tmp

print("Motion state variables: "+str(motionStateBitVars))
print("Motion control variables: "+str(motionControlBitVars))

# ====================================================================
# Assign keys to doors and deliveries
# ====================================================================
keys = []
for (a,b) in colorCoding:
    if b=="Door":
        keys.append((a,b))
    elif b=="Delivery":
        keys.append((a,b))

# ====================================================================
# Assign robot keys
# ====================================================================
movingObstacles = []
for (a,b) in colorCoding:
    if b.startswith("MovingObstacle:"):
        movingObstacles.append((a,b.split(":")))

# ==================================
# Prepare Slugs Call
# ==================================
# bddinfile = specFile
while bddinfile.rfind(".") > bddinfile.rfind(os.sep):
    bddinfile = bddinfile[0:bddinfile.rfind(".")]
bddinfile = bddinfile+".bdd"
print "Using BDD file: "+bddinfile
slugsLink = sys.argv[0][0:sys.argv[0].rfind("pyGameRobotDynamicsVisualizer.py")]+"../src/slugs"
print slugsLink

# ==================================
# Main loop
# ==================================
def actionLoop():

    screen = pygame.display.set_mode(((xsize+2)*MAGNIFY,(ysize+2)*MAGNIFY))
    pygame.display.set_caption('Strategy Visualizer')
    clock = pygame.time.Clock()

    screenBuffer = pygame.Surface(screen.get_size())
    screenBuffer = screenBuffer.convert()
    screenBuffer.fill((64, 64, 64)) # Dark Gray

    # Initialize the plot window where we will be displaying the continuous trajectory
    # fig = plt.figure()
    inflationFactor = 2  # NOTE: this takes advantage of 'unused' border cells (due to eps-inflation) to increase the effective workspace size.
    additionalImageCellsNotInStrategy = 2
    plt.axis([
        -additionalImageCellsNotInStrategy*eta-0.1,
        xsizePng*eta-additionalImageCellsNotInStrategy*eta+0.1,
        -additionalImageCellsNotInStrategy*eta-0.1,
        ysizePng*eta-additionalImageCellsNotInStrategy*eta+0.1])
    #plt.axis([xmin,xmax,ymin,ymax])
    #plt.axis([0.0,4.0,0.0,4.0])
    plt.ion()
    plt.show()
    plthdl0, = plt.plot([],[])
    plthdl1, = plt.plot([],[])
    plthdl2, = plt.plot([],[])
    img = mpimg.imread(specFile)
    imgplot = plt.imshow(img,extent=[
        -additionalImageCellsNotInStrategy*eta,
        xsizePng*eta-additionalImageCellsNotInStrategy*eta,
        ysizePng*eta-additionalImageCellsNotInStrategy*eta,
        -additionalImageCellsNotInStrategy*eta],interpolation='none')
    #plt.axvspan(-additionalImageCellsNotInStrategy*eta,(xsize-1)*eta+additionalImageCellsNotInStrategy*eta,-additionalImageCellsNotInStrategy*eta,(ysize-1)*eta+additionalImageCellsNotInStrategy*eta)
    pltH = plt.gca()
    pltH.add_patch(mpatch.Rectangle((
        -additionalImageCellsNotInStrategy*eta,
        -additionalImageCellsNotInStrategy*eta), 
        xsizePng*eta, 
        ysizePng*eta,facecolor='none',edgecolor='k'))
    plt.draw()
    #plt.savefig('temp')

    print 

    # Open Slugs
    # slugsProcess = subprocess.Popen(slugsLink+" --nonDeterministicMotionInteractiveStrategy "+slugsinfile+" "+bddinfile, shell=True, bufsize=1048000, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    slugsProcess = subprocess.Popen(slugsLink+" --environmentRefinementNonDeterministicMotion --interactiveStrategy "+slugsinfile+" "+bddinfile, shell=True, bufsize=1048000, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    # Get input APs
    slugsProcess.stdin.write("XPRINTINPUTS\n")
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    lastLine = " "
    inputAPs = []
    while (lastLine!=""):
        lastLine = slugsProcess.stdout.readline().strip()
        if lastLine!="":
            inputAPs.append(lastLine)

    # Get output APs (Motion State)
    slugsProcess.stdin.write("XPRINTMOTIONSTATE\n")
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    lastLine = " "
    outputAPs = []
    while (lastLine!=""):
        lastLine = slugsProcess.stdout.readline().strip()
        if lastLine!="":
            outputAPs.append(lastLine)

    # Get output APs (Other output)
    slugsProcess.stdin.write("XPRINTOTHEROUTPUTS\n")
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    lastLine = " "
    while (lastLine!=""):
        lastLine = slugsProcess.stdout.readline().strip()
        if lastLine!="":
            outputAPs.append(lastLine)

    # Get motion controller output APs
    slugsProcess.stdin.write("XPRINTMOTIONCONTROLOUTPUTS\n")
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    lastLine = " "
    while (lastLine!=""):
        lastLine = slugsProcess.stdout.readline().strip()
        if lastLine!="":
            outputAPs.append(lastLine)
    print "output APs:"+str(outputAPs)

    # Get initial state
    slugsProcess.stdin.write("XGETINIT\n")
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    currentState = slugsProcess.stdout.readline().strip()
    print currentState

    # Pre-store positions
    doorAndDeliveryInputBitPositions = {}
    for (a,b) in colorCoding:
        if b=="Door" or b=="Delivery":
            for pos,name in enumerate(inputAPs):
                if name=="door"+str(a) or name=="deliveryrequest"+str(a)  :
                    doorAndDeliveryInputBitPositions[a] = pos

    # run XMAKETRANS again to get a non-trivial initial state (why?)
    initInput = currentState[0:len(inputAPs)]
    slugsProcess.stdin.write("XMAKETRANS_INIT\n"+initInput)
    slugsProcess.stdin.flush()
    slugsProcess.stdout.readline() # Skip the prompt
    currentState = slugsProcess.stdout.readline().strip() 
    print currentState

    motionStateRaw = [0]*len(motionStateBitVars)
    for k in xrange(0,len(motionStateBitVars)):
        for i,ap in enumerate(outputAPs):
            for  j,ap2 in enumerate(motionStateBitVars[k]):
                if ap==ap2:
                    print i+len(inputAPs)
                    if currentState[i+len(inputAPs)]=="1":
                        motionStateRaw[k] += (1 << j)
                    elif currentState[i+len(inputAPs)]=="0":
                        pass
                    else:
                        raise 123
    motionState = np.array(motionStateRaw)*eta + np.array(minMaxStateCent[1])
    motionState = list(np.minimum(np.maximum(motionState,np.array(minMaxState[1])),np.array(minMaxState[0])))
    for i in xrange(0,len(motionState)):
        exec(motionStateVars[i]+"=motionState[i]")
        exec(motionStateVars[i]+"raw=motionStateRaw[i]")
        exec(motionStateVars[i]+"vect=["+motionStateVars[i]+"]*(numMinorIters+1)")

    loopNumber = 0
    isPaused = False
    while loopNumber < 600:
        loopNumber += 1

        for event in pygame.event.get():
            if event.type == pygame.locals.QUIT or (event.type == pygame.locals.KEYDOWN and event.key == pygame.locals.K_ESCAPE):
                slugsProcess.stdin.write("QUIT\n")
                slugsProcess.stdin.flush()
                return
            if (event.type == pygame.locals.KEYDOWN and event.key == pygame.locals.K_SPACE):
                isPaused = not isPaused

        # Obtain robot information for drawing
        motionCtrlRaw = [0]*len(motionControlBitVars)
        for k in xrange(0,len(motionControlBitVars)):
            for i,ap in enumerate(outputAPs):
                for  j,ap2 in enumerate(motionControlBitVars[k]):
                    if ap==ap2:
                        if currentState[i+len(inputAPs)]=="1":
                            motionCtrlRaw[k] += (1 << j)
                        elif currentState[i+len(inputAPs)]=="0":
                            pass
                        else:
                            raise 123
        motionCtrl = np.array(motionCtrlRaw)*mu + np.array(minMaxCtrlCent[1])
        motionCtrl = list(np.minimum(np.maximum(motionCtrl,np.array(minMaxCtrl[1])),np.array(minMaxCtrl[0])))
        for i in xrange(0,len(motionCtrl)):
            exec(motionControlVars[i]+"=motionCtrl[i]")
            exec(motionControlVars[i]+"raw=motionCtrlRaw[i]")
        # print vraw, wraw
        # print xraw, yraw, thetaraw
        # print v, w
        # print x, y, theta
        #print xraw, yraw
        #print x, y
        print 'xraw,yraw: ',xraw, yraw
        # print 'vxraw,vyraw: ',vxraw, vyraw
        # print 'u1raw,u2raw: ',u1raw, u2raw
        print 'x,y: ',x, y
        # print 'vx,vy: ',vx, vy
        # print 'u1,u2: ',u1, u2

        # Draw pickup/drop
        for i,ap in enumerate(outputAPs):
            if ap=="pickup":
                if currentState[i+len(inputAPs)]!="0":
                    fillColor = (255,64,64)
                else:
                    fillColor = (64,64,64)
                pygame.draw.rect(screenBuffer,fillColor,(0,0,MAGNIFY*(xsize+2)/2,MAGNIFY),0)
            if ap=="drop":
                if currentState[i+len(inputAPs)]!="0":
                    fillColor = (64,220,64)
                else:
                    fillColor = (64,64,64)
                pygame.draw.rect(screenBuffer,fillColor,(MAGNIFY*(xsize+2)/2,0,MAGNIFY*(xsize+2)/2,MAGNIFY),0)
            
        # Obtain moving obstacle information for drawing
        movingPos = []
        for (a,b) in movingObstacles:
            posX = 0
            posY = 0
            for i,ap in enumerate(inputAPs):
                if ap in ["mox"+str(a)+"_0","mox"+str(a)+"_1","mox"+str(a)+"_2","mox"+str(a)+"_3","mox"+str(a)+"_4","mox"+str(a)+"_5","mox"+str(a)+"_6","mox"+str(a)+"_7","mox"+str(a)+"_8","mox"+str(a)+"_9"]:
                    if currentState[i]=="1":
                        posX += (1 << int(ap[ap.rfind("_")+1:]))
                    elif currentState[i]=="0":
                        pass
                    else:
                        raise 123
                elif ap in ["moy"+str(a)+"_0","moy"+str(a)+"_1","moy"+str(a)+"_2","moy"+str(a)+"_3","moy"+str(a)+"_4","moy"+str(a)+"_5","moy"+str(a)+"_6","moy"+str(a)+"_7","moy"+str(a)+"_8","moy"+str(a)+"_9"]:
                    if currentState[i]=="1":
                        posY += (1 << int(ap[ap.rfind("_")+1:]))
            movingPos.append((posX,posY))

        # Draw Field
        for xf in xrange(0,xsizePng):
            for yf in xrange(0,ysizePng):
                paletteColor = imageData[yf*xsizePng+xf]
                
                # Translate color to what is to be written
                if paletteColor in colorCodingMap:
                    colorCodeDescription = colorCodingMap[paletteColor]
                    if colorCodeDescription.startswith("MovingObstacle:"):
                        color = (255,255,255)
                    elif colorCodeDescription=="Door" or colorCodeDescription=="Delivery":
                        if currentState[doorAndDeliveryInputBitPositions[paletteColor]]=="0":
                            color = (128+palette[paletteColor*3]/2,128+palette[paletteColor*3+1]/2,128+palette[paletteColor*3+2]/2)
                        else:
                            color = palette[paletteColor*3:paletteColor*3+3]
                    else:
                        color = palette[paletteColor*3:paletteColor*3+3]
                else:
                    color = palette[paletteColor*3:paletteColor*3+3]

                pygame.draw.rect(screenBuffer,color,((xf+1)*MAGNIFY,(yf+1)*MAGNIFY,MAGNIFY,MAGNIFY),0)

        # Draw "Good" Robot
        robotX = int(round(np.true_divide((x - xmin),eta)))
        robotY = int(round(np.true_divide((y - ymin),eta)))
        pygame.draw.circle(screenBuffer, (192,32,32), ((robotX+1)*MAGNIFY+MAGNIFY/2,(robotY+1)*MAGNIFY+MAGNIFY/2) , MAGNIFY/3-2, 0)
        pygame.draw.circle(screenBuffer, (255,255,255), ((robotX+1)*MAGNIFY+MAGNIFY/2,(robotY+1)*MAGNIFY+MAGNIFY/2) , MAGNIFY/3-1, 1)
        pygame.draw.circle(screenBuffer, (0,0,0), ((robotX+1)*MAGNIFY+MAGNIFY/2,(robotY+1)*MAGNIFY+MAGNIFY/2) , MAGNIFY/3, 1)

        plthdl0.set_xdata(np.append(plthdl0.get_xdata(), xvect))
        plthdl0.set_ydata(np.append(plthdl0.get_ydata(), yvect))
        if (any([int(currentState[0:len(inputAPs)])])):
            plthdl2.set_xdata(np.append(plthdl2.get_xdata(), x))
            plthdl2.set_ydata(np.append(plthdl2.get_ydata(), y))
            plthdl2.set_marker('o')
            plthdl2.set_linestyle('None')
            plthdl2.set_markerfacecolor('r')
        else:
            plthdl1.set_xdata(np.append(plthdl1.get_xdata(), x))
            plthdl1.set_ydata(np.append(plthdl1.get_ydata(), y))
            plthdl1.set_marker('o')
            plthdl1.set_linestyle('None')    
            plthdl1.set_markerfacecolor('y')
        plt.draw()
        plt.savefig('temp')

        # Draw cell frames
        for xc in xrange(0,xsizePng):
            for yc in xrange(0,ysizePng):
                pygame.draw.rect(screenBuffer,(0,0,0),((xc+1)*MAGNIFY,(yc+1)*MAGNIFY,MAGNIFY,MAGNIFY),1)
        pygame.draw.rect(screenBuffer,(0,0,0),(MAGNIFY-1,MAGNIFY-1,MAGNIFY*xsizePng+2,MAGNIFY*ysizePng+2),1)

        # Draw "Bad" Robot/Moving Obstacle
        for obstacleNo,(a,b) in enumerate(movingObstacles):
            speedMO = int(b[1]) # 0 or 1 - 0 is twice as slow
            xsizeMO = int(b[2])
            ysizeMO = int(b[3])
            (xpos,ypos) = movingPos[obstacleNo]
            pygame.draw.rect(screenBuffer, (32,32,192), ((xpos+1)*MAGNIFY+MAGNIFY/4,(ypos+1)*MAGNIFY+MAGNIFY/4, MAGNIFY*xsizeMO-MAGNIFY/2, MAGNIFY*xsizeMO-MAGNIFY/2),0)
            pygame.draw.rect(screenBuffer, (255,255,255), ((xpos+1)*MAGNIFY+MAGNIFY/4-1,(ypos+1)*MAGNIFY+MAGNIFY/4-1, MAGNIFY*xsizeMO-MAGNIFY/2+2, MAGNIFY*xsizeMO-MAGNIFY/2+2),1)
            pygame.draw.rect(screenBuffer, (0,0,0), ((xpos+1)*MAGNIFY+MAGNIFY/4-2,(ypos+1)*MAGNIFY+MAGNIFY/4-2, MAGNIFY*xsizeMO-MAGNIFY/2+4, MAGNIFY*xsizeMO-MAGNIFY/2+4),1)
        
        # Flip!
        screen.blit(screenBuffer, (0, 0))
        pygame.display.flip()

        # Update Doors and requests
        nextInput = currentState[0:len(inputAPs)]
        for keyNum,(a,b) in enumerate(keys):
            if pygame.key.get_pressed()[pygame.locals.K_1+keyNum]:
                nextInput = nextInput[0:doorAndDeliveryInputBitPositions[a]]+"1"+nextInput[doorAndDeliveryInputBitPositions[a]+1:]
            else:
                nextInput = nextInput[0:doorAndDeliveryInputBitPositions[a]]+"0"+nextInput[doorAndDeliveryInputBitPositions[a]+1:]

        # Update moving obstacles
        for obstacleNo,(a,b) in enumerate(movingObstacles):
            speedMO = int(b[1]) # 0 or 1 - 0 is twice as slow
            (xpos,ypos) = movingPos[obstacleNo]

            mayMove = True
            if speedMO==0:
                for i,ap in enumerate(outputAPs):
                    if ap == "MOSpeederMonitor"+str(a):
                        if currentState[i+len(inputAPs)]!="1":
                            mayMove = False

            if mayMove:
                if pygame.key.get_pressed()[pygame.locals.K_LEFT]:
                    xpos -= 1
                elif pygame.key.get_pressed()[pygame.locals.K_RIGHT]:
                    xpos += 1
                elif pygame.key.get_pressed()[pygame.locals.K_UP]:
                    ypos -= 1
                elif pygame.key.get_pressed()[pygame.locals.K_DOWN]:
                    ypos += 1

            # Encode new position
            for i,ap in enumerate(inputAPs):
                if ap in ["mox"+str(a)+"_0","mox"+str(a)+"_1","mox"+str(a)+"_2","mox"+str(a)+"_3","mox"+str(a)+"_4","mox"+str(a)+"_5","mox"+str(a)+"_6","mox"+str(a)+"_7","mox"+str(a)+"_8","mox"+str(a)+"_9"]:
                    if (xpos & (1 << int(ap[ap.rfind("_")+1:])))>0:
                        nextInput = nextInput[0:i]+"1"+nextInput[i+1:]
                    else:
                        nextInput = nextInput[0:i]+"0"+nextInput[i+1:]
                elif ap in ["moy"+str(a)+"_0","moy"+str(a)+"_1","moy"+str(a)+"_2","moy"+str(a)+"_3","moy"+str(a)+"_4","moy"+str(a)+"_5","moy"+str(a)+"_6","moy"+str(a)+"_7","moy"+str(a)+"_8","moy"+str(a)+"_9"]:
                    if (ypos & (1 << int(ap[ap.rfind("_")+1:])))>0:
                        nextInput = nextInput[0:i]+"1"+nextInput[i+1:]
                    else:
                        nextInput = nextInput[0:i]+"0"+nextInput[i+1:]

        # Execute the continuous transition
        if not isPaused:
            preMotionState = []
            for step in range(numMinorIters):
                for i,varName in enumerate(motionStateVars):
                    # one-sample update
                    #exec(varName+" = "+varName+"_dot*tau + "+varName) 
                    # create a smooth profile between points
                    exec(systemModel[i])  # update the state derivative
                    exec(varName+"vect[step] = "+varName)
                    exec(varName+" = "+varName+"_dot*tau/numMinorIters + "+varName) 
                    # print eval(varName+"_dot")
                    if varName in cyclicVars:
                        #cyclicVarDiff = eval(varName+"max-"+varName+"min")
                        #print eval("(np.floor(np.true_divide(cyclicVarDiff,eta))+1)*eta+"+varName+"min")
                        #exec("tmp="+varName+"min, "+varName+"max")
                        #if eval(varName) < -np.pi-eta/2:
                        if eval(varName) < -np.pi:
                        #if eval(varName) < eval(varName+"min-eta/2"):
                            #exec(varName+"="+varName+"+2*np.pi")
                            exec(varName+"="+varName+"+2*3.2")
                        #elif eval(varName) > np.pi+eta/2:
                        elif eval(varName) > np.pi:
                        #elif eval(varName) > eval("(np.floor(np.true_divide(cyclicVarDiff,eta))+1)*eta+"+varName+"min"):
                            #exec(varName+"="+varName+"-2*np.pi")
                            exec(varName+"="+varName+"-2*3.2")
                    else:
                        exec(varName+" = min([max(["+varName+",minMaxState[1][i]]),minMaxState[0][i]])")
            for i,varName in enumerate(motionStateVars):
                # print minMaxState[1][i], minMaxState[0][i]
                exec(varName+"vect[step+1] = "+varName) 
                #exec(varName+"raw = np.true_divide(("+varName+" - "+varName+"min),eta)")
                #exec(varName+"raw = int(np.floor(np.true_divide(("+varName+" - minMaxState[1][i]),eta)))")
                exec("tmp = np.abs([stateCent[i][j]-"+varName+" for j in range(len(stateCent[i]))])")
                #print tmp
                val,indx = min((val,indx) for (indx,val) in enumerate(tmp))
                exec(varName+"raw = indx")
                #exec(varName+"raw = int(round(np.true_divide(("+varName+" - "+varName+"min),eta)))")
                preMotionState += bin(eval(varName+'raw'))[2:].zfill(len(motionStateBitVars[i]))[::-1]  # rid ourselves of the leading '0b' and reverse BDD bit ordering
                preMotionState = ''.join(preMotionState)
            # print xvect
            # preserve the ordering in outputAPs
            preMotionStateRev = ''
            for i,ap in enumerate(outputAPs):
                for  j,ap2 in enumerate(itertools.chain(*motionStateBitVars)):
                    if ap==ap2:
                        preMotionStateRev += preMotionState[j]

            print 'input: ', nextInput
            print 'xraw,yraw (new): ',xraw, yraw
            print 'x,y (new): ',x, y

            # Make the transition
            slugsProcess.stdin.write("XMAKECONTROLTRANS\n"+nextInput+preMotionStateRev)
            slugsProcess.stdin.flush()
            slugsProcess.stdout.readline() # Skip the prompt
            nextLine = slugsProcess.stdout.readline().strip()
            print nextLine
            if nextLine.startswith("ERROR"):
                screenBuffer.fill((192, 64, 64)) # Red!
                # Keep the state the same

                print "error"

                # print vraw, wraw
                # print xraw, yraw, thetaraw
                # print v, w
                # print x, y, theta
                # sys.exit('dynamics inconsistent with robot BDD')
                # isPaused = True
            else:
                currentState = nextLine[:len(inputAPs)]+preMotionStateRev+nextLine[len(preMotionState)+1:] 
                print currentState, 'currState, iter: ',loopNumber

                # Print a state header
                if (loopNumber % 20)==1:
                    print "-"*(len(currentState)+2)
                    apNames = inputAPs+outputAPs
                    maxLenAPNames = 0
                    for a in apNames:
                        maxLenAPNames = max(maxLenAPNames,len(a))
                    apNamesEqualized = [(" "*(maxLenAPNames-len(a)))+a for a in apNames]
                    for i in xrange(0,maxLenAPNames):
                        for a in apNamesEqualized:
                            sys.stderr.write(a[i])
                        sys.stderr.write("\n")
                    print "-"*(len(currentState)+2)

                # print >>sys.stderr, currentState
                screenBuffer.fill((64, 64, 64)) # Gray, as usual
            
            # Done
            clock.tick(10)
        else:
            # Paused
            screenBuffer.fill((64, 64, 64)) # Gray, as usual
            # Tick
            clock.tick(3)


# ==================================
# Call main program
# ==================================
actionLoop()
