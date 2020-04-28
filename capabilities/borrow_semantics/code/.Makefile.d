preliminaries.vo preliminaries.glob preliminaries.v.beautified preliminaries.required_vo: preliminaries.v ./CustomTactics.vo
preliminaries.vio: preliminaries.v ./CustomTactics.vio
preliminaries.vos preliminaries.vok preliminaries.required_vos: preliminaries.v ./CustomTactics.vos
small_step.vo small_step.glob small_step.v.beautified small_step.required_vo: small_step.v ./CustomTactics.vo preliminaries.vo
small_step.vio: small_step.v ./CustomTactics.vio preliminaries.vio
small_step.vos small_step.vok small_step.required_vos: small_step.v ./CustomTactics.vos preliminaries.vos
