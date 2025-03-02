Project Objective (had to do this solo because forgot to fill out form):

The goal of this project is to model a simplified long jump competition, including the state transitions of jumpers, the management of competition time, and the interactions between jumpers, pits, and the runway. The model simulates the different stages of the competition, including when jumpers are on the runway, in the pit, and ready to jump. The model also ensures that rules are enforced, such as preventing jumpers from occupying multiple spots at once and ensuring that jumpers are correctly ordered in the competition. Overall, the model's goal is to model the flow of the competition. Initially, I wanted to model a more accurate long jump competition with the top 8 jumpers recorded, and after 3 rounds taking the top 8 jumpers and allowing them to get 3 more rounds of jumps, and finally recording the top 3 jumpers. 

Model Design and Visualization: 

The model is designed to track several key elements in a long jump competition:

Jumper State: Each jumper has a state representing their position in the competition, such as Up, OnDeck, InTheHole, and Waiting.

Time Steps: The model works over a discrete set of time steps, with each time step representing a change in the competition's progression. At each time step, jumpers move between states, and the positions of jumpers on the runway and in the pit are updated.

Runway and Pit: The runway and pit are modeled as resources that jumpers occupy during their turn. A jumper can only occupy the runway or the pit at one time, and the competition ensures that no two jumpers occupy the same spot simultaneously. 

I wrote two run statements, one for Init and one for my traces. 

The init run command is going to give you an instance of the competition that models the start. In essence this means all the jumpers, except for 3 will be in a 'Waiting' state because none of them have jumped yet. The first jumper to go will be in the 'Up' state, the second jumper will be in the 'OnDeck' state, and the third jumper will be in the 'InTheHole' state. Only one jumper can be in each of those three specific states at a time. Each jumper will also have no best jump recorded or any attempts recorded for any given time. Additionally, each jumper should point to another jumper, with all jumpers being reachable with no jumper's next fields pointing to themselves. Finally the Official should know that the first jumper is on the runway, and that the pit is clear.

The trace run command is going to give you an instance that satisfies the traces predicate at some point during the trace. The traces predicate models a state a long jump competition can be in at a given time, either the a jumper is preparing to jump, attempting their jump, or exiting the pit (ending their jump).

In general to look at and interpret an instance of my spec, look at the Jumpers compState field to know if they are or will be jumping soon (denoted by them being in a state other than 'Waiting'). The Jumper's sig attempt field maps the time they jumped to the jump distance they recorded. Look at the Official, Pit, and Runway sigs to understand who is occupying what location at a given time. 

Signatures and Predicates:

sig TIME -> 

The purpose of the TIME sig was to attach competition steps to logical TIME step events. This abstracts the concept of true time away from the competition, and hones in on the core of the model which is modeling the flow of the competition.

sig Jump ->

This sig represents a jump for each Jumper. The only field in this sig is distance. For this model we assumed that no Jumpers will found (this is a big assumption). This was done because Froglet isn't good for modeling stochastic things, which in reality would include every jump having a percent change of being a foul.

sig Jumper ->

This is one of the main sigs. This represents an athlete taking place in the competition. Each jumper knows their best jump (so far in the event), the attempts they've taken, and who the next jumper is.

sig Pit ->

This represents the long jump pit, for this model we made an assumption that there is only one long jump pit in the competition. This mimics real life, but in rare occassions (typically in really low level meets) there can be two pits. The pit knows who is in it at a specific time.

sig Runway ->

This represents the long jump runway, for this model we made an assumption that there is only one long jump runway in the competition. This mimics real life, but in rare occassions (typically in really low level meets) there can be two runway. The runway knows who is in it at a specific time.

sig Official -> 

This represents the long jump official. They know who is on the runway and in the pit at any given time, they also know who is the best jumper

pred wellformed ->

This pred essentially defines what states in the long jump competiton should always hold true. Only one jumper can be Up, OnDeck, and InTheHole at a time, the rest must be Waiting. If the Pit is occupied at a certain time the Official must also know that. If the Runway is occupied at a certain time the Official must also know that. Furthermore, each jumper can't be their own next field.

pred init ->

This pred sets up the meet. We set up some first jumper to be 'Up', the second jumper in the rotation is 'OnDeck', the third jumper is 'InTheHole'. All other jumpers are assigned a state of 'Waiting', and all the Jumper fields are cleared and set to none. We set all jumpers to be reachable from one another, with the exception of from themselves. The runway is set to be occupied by the first jumper, and the pit is emptied. The official is updated to reflect the Runway and Pit changes.

preds jumpFrameExceptState and jumpFrameExceptAttempt ->

They frame everyone but the current jumper for their attempt or state, respectively. This is called within preds that are carried out in the trace.

pred prepareToJump ->

This pred is the 'first' step in the trace. The jumper is acknowledged to be 'Up', the Runway is empty for them to step on to. The Pit isn't occupied. Then, the jumper is allowed on the Runway, the Official acknowledges them, and everything else is framed to not change.

pred attemptJump -> 

This pred is the 'second' step in the trace. The jumper attempts their jump, they move from the Runway into the Pit, and the Official is updated to reflect that. 

pred exitPit -> 

This pred is the 'last' step in the trace. The jumper exits the pit, the Official reflects that change, and gives the Jumper their Jump result. This jump is recorded by the Official and the Jumper, and the next three jumper's states are updated to allow the jumping cycle to begin again (from the prepareToJump pred)

pred traces ->

The pred defines a condition such that at all times a jumper can be either prepareToJump, attemptJump, or exitPit. Essentially, do the actions I define in the previous preds allow for the competition to run smoothly, after defining a well-defined initial competition state.

pred longJumpInvariant ->

Used in testing as something that should hold true at every trace.




