#lang forge/froglet

/*
  Long Jump Competition Model
*/

-- Each athlete is in one of these states at all times during the competition
-- Up -> Signifies the athlete is currently in the process of attempting their jump
-- OnDeck -> Signifies the athlete is next in line to attempt their jump
-- InTheHole -> Signifies the athlete is slotted to go after the athlete OnDeck
-- Waiting -> Signifies the athlete is not within three jumpers of the jumper currently attempting their jump
-- Done -> Signifies that the athlete has taken all their jumps
abstract sig CompetitionState {}
one sig Jumping, Up, OnDeck, InTheHole, Waiting extends CompetitionState {}

sig TIME {
    next: lone TIME
}

-- Jumps have an associated distance with them
sig Jump {
    distance: one Int
}

-- Represents each athlete 
sig Jumper {
    -- They know what competition state they are in
    compState: pfunc TIME -> CompetitionState,
    -- Their best jump
    best: lone Jump,
    -- The attempts they've taken
    attempts: pfunc TIME -> Jump,
    -- The next jumper
    nextJumper: one Jumper
}

-- Pit object
one sig Pit {
    -- Track who is (if any) is occupying the pit at a given TIME
    occupied: pfunc TIME -> Jumper
}

-- Runway object
one sig Runway {
    -- Track who is (if any) is occupying the runway at a given TIME
    use: pfunc TIME -> Jumper
}

-- The Long Jump Official
one sig Official {
    -- Knows who is occupying which space during a given TIME
    onRunway: pfunc TIME -> Jumper,
    inPit: pfunc TIME -> Jumper,
    -- The best jumper so far
    bestJumper: lone Jumper
}

pred wellformed {
    all t: TIME | {
        -- Only 1 jumper each can be in Up, OnDeck, and InTheHole states
        all disj j1, j2: Jumper | {
            (j1.compState[t] != Waiting and j2.compState[t] != Waiting) implies {
                j1.compState[t] != j2.compState[t]
            }
        }
        -- If the pit is occupied at a certain time, then the Official must recognize that
        Pit.occupied[t] = Official.inPit[t]
        -- If the Runway is occupied at a certain time, then the Official must recognize that
        Runway.use[t] = Official.onRunway[t]
    }

    all j: Jumper| j.nextJumper != j
}

-- Set up start of competition
pred init[t: TIME] {
    wellformed
    -- Declare firstJumper so we can reference it everywher 
    some firstJumper: Jumper | {
        firstJumper.compState[t] = Up
        firstJumper.nextJumper.compState[t] = OnDeck
        firstJumper.nextJumper.nextJumper.compState[t] = InTheHole

        all j: Jumper | {
            (j != firstJumper and j != firstJumper.nextJumper and j != firstJumper.nextJumper.nextJumper) implies {
                j.compState[t] = Waiting
            }
            no j.best
            no j.attempts[t]
             -- nextJumper cannot be yourself
            j.nextJumper != j
        }
        -- All jumpers are reachable 
        all disj j1, j2: Jumper {
            reachable[j2, j1, nextJumper]
        }

        -- Set Runway
        Runway.use[t] = firstJumper

         -- Set Pit
        no Pit.occupied[t]

        -- Set up the long jump official
        Official.onRunway[t] = firstJumper
        no Official.inPit[t]
        no Official.bestJumper
    }
}

pred jumpFrameExceptState[t1, t2: TIME, currJumper: Jumper] {
    all j: Jumper | {
        (j != currJumper) implies {
            j.compState[t1] = j.compState[t2]
        }
        j.attempts[t1] = j.attempts[t2]
    }
}

pred jumpFrameExceptAttempt[t1, t2: TIME, currJumper: Jumper] {
    all j: Jumper | {
        (j != currJumper) implies {
            j.attempts[t1] = j.attempts[t2]
        }
        (j != currJumper and j!= currJumper.nextJumper and j!= currJumper.nextJumper.nextJumper and j != currJumper.nextJumper.nextJumper.nextJumper) implies {
            j.compState[t1] = j.compState[t2]
        }
    }
}

pred prepareToJump[t1, t2: TIME, j: Jumper] {
    j.compState[t1] = Up    -- guard: Jumper should be OnDeck before stepping on to Runway
    no Runway.use[t1]   -- guard: no one on runway 
    no Official.onRunway[t1]    -- guard: Official isn't actively watching anyone
    no Pit.occupied[t1]    -- guard: Pit is empty
    no Official.inPit[t1]    -- guard: Official knows pit is empty

    j.compState[t2] = Up    -- action: Update the Jumpers compState
    Runway.use[t2] = j    -- action: Update runway with current jumper
    Official.onRunway[t2] = j    -- action: Official acknowledges you on the runway

    jumpFrameExceptState[t1, t2, j] -- frame: All other jumpers should not be changing their states and no one should be taking any attempts

    Official.inPit[t1] = Official.inPit[t2] -- frame: Official's view of the pit isn't changing
    Pit.occupied[t1] = Pit.occupied[t2] -- frame: Pit is empty
}

pred attemptJump[t1, t2: TIME, j: Jumper] {
    j.compState[t1] = Up    -- guard: Jumper should be Up before jumping
    Runway.use[t1] = j   -- guard: Jumper attempting the jump is on the Runway 
    Official.onRunway[t1] = j    -- guard: Official isn't actively watching anyone
    no Pit.occupied[t1]    -- guard: Pit is empty
    no Official.inPit[t1]    -- guard: Official knows pit is empty

    no Runway.use[t2]  -- action: Update runway to be empty (signifies Jumper has jumped)
    no Official.onRunway[t2] -- action: Official acknowledges Jumper is carryout out the jump on the runway
    Pit.occupied[t2] = j  -- action: Update pit to have the Jumper (signifies Jumper has completed the Jump)
    Official.inPit[t2] = j -- action: Official acknowledges Jumper is in the Pit

    j.compState[t2] = Waiting   -- action: Update the Jumpers compState to Waiting

    jumpFrameExceptState[t1, t2, j] -- frame: All other jumpers should not be changing their states and no one should be taking any attempts
}

pred exitPit[t1, t2: TIME, j: Jumper] {
    j.compState[t1] = Waiting    -- guard: Jumper should be Up before jumping
    Pit.occupied[t1] = j    -- guard: Pit is occupied by the jumper
    Official.inPit[t1] = j    -- guard: Official recognizes the pit is occupied

    no Pit.occupied[t2]  -- action: Update pit to be empty (signifies Jumper has completed the Jump)
    no Official.inPit[t2] -- action: Official acknowledges Jumper has carried out their jump

    -- Assign a jump to the Jumper
    one jump: Jump | {
        j.attempts[t2] = jump
        (j.best.distance < jump.distance) implies {
            j.best = jump
        }
        (Official.bestJumper.best.distance < j.best.distance) implies {
            Official.bestJumper = j
        }
    }
    j.compState[t2] = Waiting   -- action: Update the Jumpers compState to Waiting
    j.nextJumper.compState[t2] = Up   -- action: Update the next Jumpers compState to Up
    j.nextJumper.nextJumper.compState[t2] = OnDeck   -- action: Update the next next Jumpers compState to OnDeck
    j.nextJumper.nextJumper.nextJumper.compState[t2] = InTheHole   -- action: Update the next next Jumpers compState to InTheHole

    jumpFrameExceptAttempt[t1, t2, j]
}

pred traces {
    some firstState: TIME | some lastState: TIME | {
        init[firstState] 
        no t: TIME | t.next = firstState // JC: Can't have time before firstState
        no lastState.next  //JC: Can't have time after lastState
        some t: TIME | t != lastState implies {
            // JC: At some time not lastState we will always be able to have at least one action to take
            some j: Jumper | {
                prepareToJump[t, t.next, j] or
                attemptJump[t, t.next, j] or
                exitPit[t, t.next, j]
            }
        }
    }
}

pred longJumpInvariant {
    -- Only one jumper can be in the pit at a time
    all t: TIME | lone Pit.occupied[t]

    all t: TIME | lone Runway.use[t]

    all t: TIME | {
        lone j: Jumper | j.compState[t] = Up
        lone j: Jumper | j.compState[t] = OnDeck
        lone j: Jumper | j.compState[t] = InTheHole
    }
}


testInit: run { 
    some t: TIME | init[t]
} for exactly 1 TIME for {next is linear}

testTrace: run {
    traces
} for {next is linear}

-------------------------TESTING-------------------------

test expect {

    -- Test that jumper can occupy a pit at a certain time
    jumperCanOccupyPit: {       
        some t: TIME, j: Jumper | {            
            Pit.occupied[t.next] = j             
        }
    } for exactly 4 Jumper, 8 TIME for {next is linear} is sat

    -- Test that jumper can occupy runway
    jumperCanOccupyRunway: {       
        some t: TIME, j: Jumper | {            
            Runway.use[t.next] = j             
        }
    } for 4 Jumper, 8 TIME for {next is linear} is sat

    -- Test that at some point a jumper is preparing to jump
    jumperCanPrepareToJump: {
        some t: TIME, j: Jumper | {
            prepareToJump[t, t.next, j]
        }
    } for 4 Jumper, 8 TIME for {next is linear} is sat

    -- Test that at some point a jumper is attempting to jump
    jumperCanAttemptToJump: {
        some t: TIME, j: Jumper | {
            attemptJump[t, t.next, j]
        }
    } for 3 Jumper, 8 TIME for {next is linear} is sat

    -- Test that at some point a jumper is exiting the jump attempt, which indicates they succesfully jumped
    jumperCanExitJump: {
        some t: TIME, j: Jumper | {
            wellformed
            exitPit[t, t.next, j]
        }
    } for {next is linear} is sat

}

test suite for Init {
    assert all t: TIME | {init[t]} is sufficient for longJumpInvariant
}

test suite for Trace {
    assert all t: TIME | {traces} is sufficient for longJumpInvariant
    assert all t: TIME | {traces} is sufficient for wellformed
}