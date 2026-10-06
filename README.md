=== GARANTIER ===
1. Ingen frame er udleveret to gange samtidig.
2. alloc udleverer kun frie frames, og de nægter områder med udleverede frames.
3. dealloc tager kun udleverede frames, så double free er umuligt for verificerede kaldere.
4. Ingen overflow, ingen indeksering uden for bitmappet, ingen panics, og alle løkker stopper

=== INGEN GARANTI ===
- Egenskaber som ikke står i specifikationenen
- At værktøjer er korrekte: Verus, Z3, Rust-compileren og vstd's antagelser.
- At uverificeret kalderer overholder requires. Runtime-tjekket i dealloc fanger kun double free, skæve adresser og adresser uden for bitmappet.
- At områderne givet til add_region faktisk er ledig RAM
- At ingen bruger en frame efter dealloc (use-after-free) 
- At det er sikkert at bruge den fra flere tråde. Det kræver en lås udenom
- Hukommelse over 4 GiB, som ikke bliver brugt.
