Definition verdict_maybe : word := Z_to_bv 64 2.

Definition classifier_total3_T_fo (Cl : Image) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry Cl en (to_proc_input f) ->
      must_exit_with_scfg forced_only_cfg verdict_accept Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_reject Cl classifier_alloc_limit en (to_proc_input f)
      \/ must_exit_with_scfg forced_only_cfg verdict_maybe Cl classifier_alloc_limit en (to_proc_input f).

Definition says_no_fo (C : Image) (f : FinProcInput) : Prop :=
  forall en,
    valid_entry C en (to_proc_input f) ->
    must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f).

Definition maybe_fo (C : Image) (f : FinProcInput) : Prop :=
  valid_fin_input f /\ ~ accepts_fo C f /\ ~ says_no_fo C f.

Definition sound_fo (C : Image) (spec : ProcInput -> Prop) : Prop :=
  forall f : FinProcInput,
    valid_fin_input f ->
    forall en,
      valid_entry C en (to_proc_input f) ->
      (must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en (to_proc_input f)
       -> spec (to_proc_input f))
      /\ (spec (to_proc_input f)
          -> ~ must_exit_with_scfg forced_only_cfg verdict_reject C classifier_alloc_limit en (to_proc_input f)).

Definition maybe_empty_T_fo (C : Image) : Prop := forall f, ~ maybe_fo C f.

Definition classifies_good_inputs_sound_T_s (cfg : SpuriousCfg) (O1 O2 C : Image) : Prop :=
  sound_fo C (good_input_s cfg O1 O2).

Definition classifies_patch_diff_sound_T_s (cfg : SpuriousCfg) (O1 P1 O2 P2 C : Image) : Prop :=
  sound_fo C (fun inp => agree_s cfg O1 P1 source_alloc_limit inp
                         /\ agree_s cfg O2 P2 target_alloc_limit inp).

Definition maybe_bound_T_fo (C : Image) (w : FinProcInput -> Q) (M b : Q) : Prop :=
  forall l : list FinProcInput,
    List.NoDup (List.map fin_core l) ->
    (forall f, In f l -> maybe_fo C f) ->
    (sum_weights w l <= b * M)%Q.
