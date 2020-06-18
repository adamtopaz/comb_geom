import tactic

/-- A silly macro. -/
meta def tiny_hammer := `[{finish} <|> {tidy, finish} <|> {simp} <|> {dsimp}]