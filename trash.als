
// Phase 1: Structural Model

// People
sig Person {}

// Materials (cargo)
sig Material {}

// Locations
abstract sig Location {}
sig Dwelling, Warehouse, Workplace extends Location {}

// Vehicles
abstract sig Vehicle {}
sig PassengerVehicle extends Vehicle {
    maxSeats: Int
}
sig CargoVehicle extends Vehicle {
    maxCapacity: Int
}

// Workplaces specify requirements
sig Workplace extends Location {
    requiredPeople: Int,
    requiredMaterials: Int
}

// Assign people and materials to locations (optional initial placement)
sig Placement {
    people: set Person,
    materials: set Material,
    location: one Location
}

// Vehicle capacities should be positive
fact vehicleCapacity {
    all v: PassengerVehicle | v.maxSeats > 0
    all v: CargoVehicle | v.maxCapacity > 0
}

// Workplaces require at least one person and one material
fact workplaceRequirements {
    all w: Workplace | w.requiredPeople >= 1 and w.requiredMaterials >= 1
}

// Initial configuration generator
pred initConfig {
    // Every person and material starts somewhere
    all p: Person | some pl: Placement | p in pl.people
    all m: Material | some pl: Placement | m in pl.materials
}

// Run Alloy to visualize
run initConfig for 5 Person, 5 Material, 2 Dwelling, 2 Warehouse, 2 Workplace, 
    2 PassengerVehicle, 2 CargoVehicle, 10 Placement
