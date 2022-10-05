enum Status {Unborn, Alive, Dead}

abstract sig Person {
  var children : set Person,
  var spouse : lone Person,
  var status : one Status
}

sig Man, Woman extends Person {}

enum Operator { Death, Birth, Marriage, Other }

one sig Track { var op : lone Operator }

-- Utils

pred isAlive [p : Person] {
  p.status = Alive
}

pred isDead [p : Person] {
  p.status = Dead
}

fun LivingPeople : Person { status.Alive }

pred noChildrenChanged [ Ps : set Person ] {
  all p : Ps | p.children' = p.children
}

pred noSpouseChanged [ Ps : set Person ] {
  all p : Ps | p.spouse' = p.spouse
}

pred noStatusChanged [ Ps : set Person ] {
  all p : Ps | p.status' = p.status
}

pred BloodRelatives [p, q : Person] {
  some a : Person | (p + q) in a.*children
}

-- Operations

pred dies [p : Person] {
  -- pre-condition: be alive
  isAlive[p]
  -- post-condition
  after isDead[p]

  -- frame conditions (fully determining the next state)
  noStatusChanged[Person - p]
  noChildrenChanged[Person]
  noSpouseChanged[Person]

  Track.op' = Death
}

pred getMarried [p, q : Person] {
  -- pre-condition
  isAlive[p] and isAlive[q]
  no (p + q).spouse
  not BloodRelatives[p,q]

  -- post-condition
  after q in p.spouse
  after p in q.spouse

  -- frame conditions
  noStatusChanged[Person]
  noSpouseChanged[Person - (p + q)]
  noChildrenChanged[Person]

  Track.op' = Marriage
}

pred isBornFromParents [p: Person, m: Man, w: Woman] {
  -- pre-condition
  p.status = Unborn
  isAlive[w]
  once isAlive[m]

  -- post-condition
  after isAlive[p]
  --w.children' = w.children + p
  --m.children' = m.children + p
  children' = children + (m -> p) + (w -> p)

  -- frame conditions
  noSpouseChanged[Person]
  noStatusChanged[Person - p]
  noChildrenChanged[Person - (m + w)]

  Track.op' = Birth
}

pred other {
  noStatusChanged[Person]
  noChildrenChanged[Person]
  noSpouseChanged[Person]

  Track.op' = Other
}

--pred getMarried [p, q : Person]

-------------------------
-- Inital conditions
-------------------------

pred init {
  no children
  no spouse
  no status.Dead
  #Person > #LivingPeople
  some Man & LivingPeople
  some Woman & LivingPeople
}

----------------------------
-- Transition Relation
----------------------------

pred transition {
  (some p : Person | dies[p])
  or (some p, q : Person | getMarried[p, q])
  or (some p : Person, m : Man, w : Woman |
           isBornFromParents[p,m,w])
  or other
}

-----------------------------
-- Transition system
---------------------------

pred System {
  init
  always transition
}

run {
  System
  eventually ( some p, q : Person | getMarried[p, q] )
  eventually ( all p : Person | not p.status = Unborn )

  -- while somebody is alive, something happens. Note this forces
  -- everybody to die.
  Track.op != Other until all p : Person | p.status = Dead
 }

-- Nobody can be their own ancestor
assert nobodyCanBeTheirOwnAncestor {
  always (System => no p : Person | p in p.^children)
}
--check nobodyCanBeTheirOwnAncestor for 5 but 6 steps
check nobodyCanBeTheirOwnAncestor for 5 but 6 steps
