
// Logistics Model: Phase 1 + Phase 2

// People and Materials
sig Person {}
sig Material {}

// Locations
abstract sig Location {}
sig Dwelling, Warehouse, Workplace extends Location {}

// Workplaces specify requirements
sig Workplace extends Location {
    requiredPeople: Int,
    requiredMaterials: Int
}

// Vehicles
abstract sig Vehicle {}

sig PassengerVehicle extends Vehicle {
    maxSeats: Int,
    passengers: set Person
}

sig CargoVehicle extends Vehicle {
    maxCapacity: Int,
    cargo: set Material
}
// Assign people and materials to locations
sig Placement {
    people: set Person,
    materials: set Material,
    location: one Location
}
// Phase 1 Facts

// Vehicle capacities must be positive
fact vehicleCapacity {
    all v: PassengerVehicle | v.maxSeats > 0
    all v: CargoVehicle | v.maxCapacity > 0
}

// Workplaces require at least 1 person and 1 material
fact workplaceRequirements {
    all w: Workplace | w.requiredPeople >= 1 and w.requiredMaterials >= 1
}

// Vehicles cannot exceed capacity
fact capacityLimits {
    all v: PassengerVehicle | #v.passengers <= v.maxSeats
    all v: CargoVehicle | #v.cargo <= v.maxCapacity
}

// Optional: People/materials cannot be in multiple vehicles
fact uniqueAssignments {
    all p: Person | lone v: PassengerVehicle | p in v.passengers
    all m: Material | lone v: CargoVehicle | m in v.cargo
}
// Phase 1 Initial Configuration
pred initConfig {
    // Every person and material starts somewhere
    all p: Person | some pl: Placement | p in pl.people
    all m: Material | some pl: Placement | m in pl.materials
}
// Phase 2 Dynamic Actions

// Move a person from a location using a passenger vehicle
pred movePerson[p: Person, from: Location, to: Location, v: PassengerVehicle] {
    // Guard: person is at 'from' and vehicle has space
    some pl: Placement | p in pl.people and pl.location = from
    #v.passengers < v.maxSeats
    
    // Effect: person is now in vehicle and at 'to'
    p in v.passengers
    some pl': Placement | p in pl'.people and pl'.location = to
}

// Move a material from a location using a cargo vehicle
pred moveMaterial[m: Material, from: Location, to: Location, v: CargoVehicle] {
    // Guard: material is at 'from' and vehicle has space
    some pl: Placement | m in pl.materials and pl.location = from
    #v.cargo < v.maxCapacity
    
    // Effect: material is now in vehicle and at 'to'
    m in v.cargo
    some pl': Placement | m in pl'.materials and pl'.location = to
}

// Complete a job at a workplace
pred completeJob[w: Workplace] {
    // Guard: enough people and materials have arrived
    #({p: Person | some pl: Placement | p in pl.people and pl.location = w}) >= w.requiredPeople
    #({m: Material | some pl: Placement | m in pl.materials and pl.location = w}) >= w.requiredMaterials
    
}
//Transition Fact for Alloy simulation
fact trans {
    always (
        some p: Person, from, to: Location, v: PassengerVehicle | movePerson[p, from, to, v] or
        some m: Material, from, to: Location, v: CargoVehicle | moveMaterial[m, from, to, v] or
        some w: Workplace | completeJob[w]
    )
}
// Run Alloy to visualize
run initConfig for 5 Person, 5 Material, 2 Dwelling, 2 Warehouse, 2 Workplace, 
    2 PassengerVehicle, 2 CargoVehicle, 10 Placement
