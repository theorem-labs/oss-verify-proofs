(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record pm_syms : Type := PMS {
  ps_tid : Z;                 (* [comment removed for export] *)
  ps_granted : bool;          (* [comment removed for export] *)
  ps_b04 : Z; ps_b05 : Z; ps_b06 : Z; ps_b08 : Z; ps_b09 : Z; ps_b10 : Z; ps_b11 : Z; ps_b12 : Z;
  ps_b13 : Z;                 (* [comment removed for export] *)
  ps_b16 : Z; ps_b20 : Z; ps_b21 : Z; ps_b22 : Z; ps_b23 : Z; ps_b24 : Z;
  ps_b19r : Z;
  ps_a1 : Z; ps_a2 : Z; ps_a3 : Z;                  (* [comment removed for export] *)
  ps_g1 : Z; ps_g2 : Z; ps_g3 : Z; ps_g4 : Z        (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition AIMG_LO : Z := 0x10000.          (* [comment removed for export] *)
Definition AIMG_TOP : Z := 0xc04000.
Definition ALOWSH_LO : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition AHI_LO : Z := 0x10007fff8000.

(* [comment removed for export] *)
Definition page_up (z : Z) : Z := ((z + 4095) / 4096) * 4096.
Definition page_down (z : Z) : Z := (z / 4096) * 4096.
(* [comment removed for export] *)
Definition pm_sh (a : Z) : Z := 0x7fff8000 + a / 8.
(* [comment removed for export] *)
Definition pm_top (sp0z : Z) : Z := sp0z - 0x800000.
(* [comment removed for export] *)
Definition pm_stack_top (sp0z : Z) : Z := page_up (sp0z - 0xa0).
Definition pm_stack_bottom (sp0z : Z) : Z := pm_stack_top sp0z - 0x800000.
(* [comment removed for export] *)
Definition pm_space_beg (X : pm_syms) : Z := ((ps_b06 X) / 0x10000) * 0x10000 + 0x10000.
Definition pm_region_info (X : pm_syms) : Z := pm_space_beg X + 2^37.        (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_A15 (sp0z : Z) : Z := page_up (pm_sh (pm_stack_bottom sp0z)).
Definition pm_E15 (sp0z : Z) : Z := page_down (pm_sh (pm_stack_top sp0z)).
Definition pm_r (sp0z : Z) : Z := (pm_sh (pm_stack_top sp0z)) mod 4096.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition pm_short (sp0z : Z) : bool := (0x60 <=? sp0z mod 4096) && (sp0z mod 4096 <=? 0xa0).
(* [comment removed for export] *)
Definition pm_meta_map (brk0z : Z) (X : pm_syms) : Z := if (ps_granted X) then brk0z else (ps_b19r X).
(* [comment removed for export] *)
Definition pm_envp (sp0z argc : Z) : Z := sp0z + 16 + 8 * argc.
Definition pm_auxv (sp0z argc envc : Z) : Z := pm_envp sp0z argc + 8 * (envc + 1).
Definition pm_argv0 (sp0z argc envc : Z) : Z := pm_auxv sp0z argc envc + 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pm_kernel_placed (X : pm_syms) : list (Z * Z) :=   (* [comment removed for export] *)
  [((ps_b04 X), 0x10000); ((ps_b05 X), 0x38e000); ((ps_b06 X), 0x2000011000); ((ps_b08 X), 0x800000);
   ((ps_b09 X), 0x1000); ((ps_b10 X), 0x10000); ((ps_b11 X), 0x1000); ((ps_b12 X), 0x1000); ((ps_b16 X), 0xb09000);
   ((ps_b20 X), 0x1000); ((ps_b21 X), 0x100000); ((ps_b22 X), 0x800000); ((ps_b23 X), 0x1000);
   ((ps_a1 X), 0x10000); ((ps_a2 X), 0x10000); ((ps_a3 X), 0x10000); ((ps_b24 X), 0x10000)]
  ++ (if (ps_granted X) then [] else [((ps_b19r X), 0x2000)]).

Fixpoint pairwise_apart (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => Forall (fun q => a + n <= fst q \/ fst q + snd q <= a) r /\ pairwise_apart r
  end.

(* [comment removed for export] *)
Definition pm_placed (sp0z : Z) (p : Z * Z) : Prop :=
  fst p mod 4096 = 0 /\ 4096 <= fst p /\ fst p + snd p <= pm_top sp0z
  /\ (fst p + snd p <= AIMG_LO \/ AIMG_TOP <= fst p)
  /\ (fst p + snd p <= ALOWSH_LO \/ AHI_LO <= fst p).

(* [comment removed for export] *)
Definition pm_band3 (sp0z : Z) (X0 n : Z) : Prop :=
  (4096 <= X0 /\ X0 + n <= AIMG_LO) \/ (AIMG_TOP <= X0 /\ X0 + n <= ALOWSH_LO) \/ (AHI_LO <= X0 /\ X0 + n <= pm_top sp0z).

Lemma pm_placed_band3 : forall sp0z p, pm_placed sp0z p -> 0 <= snd p -> pm_band3 sp0z (fst p) (snd p).
Proof.
  intros sp0z [a n] (H1 & H2 & H3 & H4 & H5) Hn. unfold pm_band3, AIMG_LO, AIMG_TOP, ALOWSH_LO, AHI_LO in *. cbn [fst snd] in *. lia.
Qed.

Record pm_syms_ok (sp0z brk0z mbasez : Z) (X : pm_syms) : Prop := PMSOK {
  pso_tid    : 0 < (ps_tid X) < 2^22;                       (* [comment removed for export] *)
  pso_placed : Forall (pm_placed sp0z) (pm_kernel_placed X);
  pso_apart  : pairwise_apart (pm_kernel_placed X);                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  pso_spacebeg : (ps_b06 X) < pm_space_beg X <= (ps_b06 X) + 0x10000 /\ pm_space_beg X mod 0x10000 = 0;
  pso_brk    : (ps_granted X) = true ->
               brk0z + 0x3000 <= ALOWSH_LO                                               (* [comment removed for export] *)
               /\ Forall (fun q => brk0z + 0x2000 <= fst q \/ fst q + snd q <= brk0z) (pm_kernel_placed X)
}.
