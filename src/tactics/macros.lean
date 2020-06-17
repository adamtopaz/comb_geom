import tactic

meta def tiny_hammer := `[{finish} <|> {tidy, finish} <|> {simp} <|> {dsimp}]