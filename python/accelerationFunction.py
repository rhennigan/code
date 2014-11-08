# QUIZ
#
# Modify the acceleration function so that it returns 
# the acceleration vector of the spacecraft.
#
# A sample of how to use the numpy.linalg.norm function
# is given. This computes the length of the vector, and 
# it should be the only outside function you need to 
# use in your answer.

import numpy

earth_mass = 5.97e24 # kg
moon_mass = 7.35e22 # kg
gravitational_constant = 6.67e-11 # N m2 / kg2

# The origin, or (0,0), is at the center of the earth 
# in this example, so it doesn't make any sense to 
# set either the moon_position or spaceship_position
# equal to (0,0). Depending on your solution, doing this
# may throw an error!  Please note that moon_position and 
# spaceship_position are both numpy arrays, and the 
# returned value should also be a numpy array.

def acceleration(moon_position, spaceship_position):
    nonsense = numpy.linalg.norm(moon_position) * spaceship_position
    return nonsense

acceleration((5,0),(0,-1))
