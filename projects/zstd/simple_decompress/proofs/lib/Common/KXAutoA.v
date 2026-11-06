(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import KXStepR KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan.
Import ListNotations.
Import KXS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive kza : Type :=
| KAUnp (a n : Z)      (* [comment removed for export] *)
| KAApp (a n : Z)      (* [comment removed for export] *)
| KAShp (s x : Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TRunA.
Variable segs : list Segment.

Definition kx_trunA (vmax : Z) (akn : list aent) (fuel : nat) (stops : list Z) (scalls : bool) (pc : Z) (rz : list zexp)
                    (zks : list zk) (rk : list kentry) (rs ws : list zreg) (nz : nat)
  : ktreeA * vtree * list rdspec * list kentry * list expr :=
  let kn := map zk_kentry zks ++ rk in
  let t := kx_treeA segs vmax akn fuel true stops scalls (kt_init pc rz kn nz) [] [] [] in
  let reads := kx_reads_of nz (kta_next t) (kta_scs t) in
  (t, kta_resid akn kn rs ws [] t, reads, kx_rk (map zk_kentry zks) (zk_tfs zks) nz reads, map zx rz).

End TRunA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma unpoisoned_unpZ : forall (m : word -> option byte) lo hi lo' hi',
  unpoisoned m lo hi -> lo <= lo' -> hi' <= hi -> hi' <= KXKEND -> unpZ m lo' hi'.
Proof.
  intros m lo hi lo' hi' U H1 H2 H3.
  pose proof (unpoisoned_sub m lo hi lo' hi' U H1 H2) as (A & B & H).
  split; [exact A|]. split; [exact H3|]. intros G G0 G1 G2.
  destruct (H G G0 G1 G2) as (b & Hb & Hok). exists b. split; [exact Hb | exact Hok].
Qed.

Lemma shad_shspan_rng : forall RNG A n A0 N0,
  rng RNG A0 N0 -> A0 <= shad A -> shad A + shspanZ A n <= A0 + N0 -> 0 <= A ->
  rng RNG (KXSHLO + A / 8) (shspanZ A n).
Proof.
  intros RNG A n A0 N0 H H1 H2 H3. rewrite shad_div in H1, H2. unfold ASHOFF in H1, H2. unfold KXSHLO.
  eapply rng_sub'; [exact H | lia].
Qed.

(* [comment removed for export] *)
Ltac kxa_unp_hook := fail.
Ltac kxa_rng_hook := fail.
Ltac kxa_app_hook := fail.
(* [comment removed for export] *)
Ltac kxa_norm := idtac.

(* [comment removed for export] *)
Ltac kxa_hyp := lazymatch goal with |- ?G => match goal with H : G |- _ => exact H end end.

Ltac kxa_unpZ :=
  lazymatch goal with
  | |- unpZ ?m ?lo ?hi =>
      first [ kxa_hyp
            | match goal with
              | U : unpoisoned m ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ m lo0 hi0 lo hi U); solve [unfold KXKEND; kx_lia]
              end
            | kxa_unp_hook ]
  end.

Ltac kxa_rng0 :=
  kxa_norm;
  lazymatch goal with
  | |- rng ?RNG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
      first [ match goal with
              | H : rng RNG (shad ?A0) ?N0 |- _ =>
                  apply (shad_shspan_rng RNG A n (shad A0) N0 H);
                  [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              | H : rng RNG ?A0 ?N0 |- _ =>
                  apply (shad_shspan_rng RNG A n A0 N0 H);
                  [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              end
            | (* [comment removed for export] *)
              lazymatch RNG with
              | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
              end
            | kxa_rng_hook ]
  end.
(* [comment removed for export] *)
Ltac kxa_rng := first [ kxa_hyp | kxa_rng0 ].

Ltac kxa_zak_pre := lazy beta iota zeta delta [zak_prop zspan_ok]; kx_zoffs; lazy beta iota zeta delta [zden znth].
Ltac kxa_zak_solve :=
  lazymatch goal with
  | |- _ /\ unpZ _ _ _ /\ _ => split; [kx_lia | split; [kxa_unpZ | intros _; kxa_rng]]
  | |- _ /\ _ <= KXKEND /\ _ => first [ unfold KXKEND, KXSHLO, KXSHHI; solve [repeat split; kx_lia] | unfold KXKEND, KXSHLO, KXSHHI; solve [lia] | kxa_app_hook ]
  | |- _ /\ _ = KXSHLO + _ / 8 => unfold KXSHLO; split; [kx_lia | first [reflexivity | kx_lia | lia]]     (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Ltac kxa_zaks_solve :=
  repeat (apply Forall_cons; [kxa_zak_pre; try solve [kxa_zak_solve]|]); try apply Forall_nil.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac kx_rak1 l k :=
  lazymatch k with
  | KAUnp ?a ?n =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) => constr:((l2, ZAUnp ea en)) end end
  | KAApp ?a ?n =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) => constr:((l2, ZAApp ea en)) end end
  | KAShp ?a ?n =>
      let r1 := kx_rz l a in lazymatch r1 with (?l1, ?ea) =>
      let r2 := kx_rz l1 n in lazymatch r2 with (?l2, ?en) => constr:((l2, ZAShp ea en)) end end
  end.
Ltac kx_raks l ks :=
  lazymatch ks with
  | @nil _ => constr:((l, @nil zak))
  | @cons _ ?k ?t =>
      let r1 := kx_rak1 l k in
      lazymatch r1 with (?l1, ?k1) =>
        let r2 := kx_raks l1 t in
        lazymatch r2 with (?l2, ?ks') => constr:((l2, @cons zak k1 ks')) end end
  end.

(* [comment removed for export] *)
Ltac kxa_kzs_ext AKS KZS :=
  lazymatch AKS with
  | @nil _ => KZS
  | @cons _ (KAShp ?s ?x) ?t => let K := kxa_kzs_ext t KZS in constr:(@cons kz (KZRange (x / 8) 0 17592186044416) K)
  | @cons _ _ ?t => kxa_kzs_ext t KZS
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kx_trunA_fix segs VMAX akn FUEL stops scalls pcv rz zks rk rs ws nz n :=
  let out := eval vm_compute in (kx_trunA segs VMAX akn FUEL stops scalls pcv rz zks rk rs ws nz) in
  lazymatch out with
  | (?t, ?r, ?reads, ?rk', ?es0) =>
      let same := eval vm_compute in (kentry_list_eqb rk rk') in
      lazymatch same with
      | true => constr:((out, rk))
      | false =>
          lazymatch n with
          | O => fail 100 "kx_autoA: the fresh-read range facts do not stabilise"
          | S ?n' => kx_trunA_fix segs VMAX akn FUEL stops scalls pcv rz zks rk' rs ws nz n'
          end
      end
  end.

Ltac kx_report_tree t :=
  let nl := eval vm_compute in (Z.of_nat (kta_leaves t)) in
  let nc := eval vm_compute in (Z.of_nat (kta_checks t)) in
  idtac "kx_autoA:" nl "leaves," nc "native ASan checks".

(* [comment removed for export] *)
Ltac kx_autoA_core VMAX STOPS FUEL SCALLS AKS KZS RRS :=
  let KZS := kxa_kzs_ext AKS KZS in
  kx_mkR_fold;
  lazymatch goal with
  | |- evt ?segs ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kx_add_cells segs m l2a zks0 in
      lazymatch r2b with (?l2c, ?zks1) =>
      let zks := kx_add_wrimgs segs m l2c KZS zks1 in
      let ra := kx_raks l2c AKS in
      lazymatch ra with (?l2, ?aks) =>
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?zs, ?rs) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let akn := eval vm_compute in (map zak_aent aks) in
      let res := kx_trunA_fix segs VMAX akn FUEL stops SCALLS pcv rz zks (@nil kentry) rs (@nil zreg) nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          kx_report_tree t;
          change (evt segs Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_treeA_evt segs F fc Q VMAX FUEL stops SCALLS zs rz xs zks rk aks pcv m rom t r reads rs _ _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktreeA t)
          | kx_cert
          | kx_regs_eqs
          | kx_zks_solve
          | kx_zregs_solve
          | kxa_zaks_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_split segs Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end end
  end.

(* [comment removed for export] *)
Ltac kx_autoFA_core VMAX STOPS FUEL SCALLS AKS KZS RRS WWS :=
  let KZS := kxa_kzs_ext AKS KZS in
  kx_mkR_fold;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kx_add_cells segs m l2a zks0 in
      lazymatch r2b with (?l2c, ?zks1) =>
      let zks := kx_add_wrimgs segs m l2c KZS zks1 in
      let ra := kx_raks l2c AKS in
      lazymatch ra with (?l2, ?aks) =>
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?l3, ?rs) =>
      let r4 := kx_rrs l3 WWS in
      lazymatch r4 with (?zs, ?ws) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let akn := eval vm_compute in (map zak_aent aks) in
      let res := kx_trunA_fix segs VMAX akn FUEL stops SCALLS pcv rz zks (@nil kentry) rs ws nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          kx_report_tree t;
          change (evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_treeA_evtF segs F fc RNG Q VMAX FUEL stops SCALLS zs rz xs zks rk aks pcv m rom t r reads rs ws _ _ _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktreeA t)
          | kx_cert
          | kx_regs_eqs
          | kx_zks_solve
          | kx_zregs_solve
          | kx_zwins_solve
          | kxa_zaks_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end end end
  end.

(* [comment removed for export] *)
Ltac kx_autoFLA_core VMAX STOPS FUEL SCALLS CH AKS KZS RRS WWS :=
  let KZS := kxa_kzs_ext AKS KZS in
  kx_mkR_fold;
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                             ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
      let xs := constr:([x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20;
                         x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31]) in
      let pcv := eval vm_compute in pc in
      let r1 := kx_rws (@nil Z) xs in
      lazymatch r1 with (?l1, ?rz) =>
      let r2 := kx_rks l1 KZS in
      lazymatch r2 with (?l2a, ?zks0) =>
      let r2b := kxl_named l2a CH in
      lazymatch r2b with (?l2c, ?cp, ?ds) =>
      let extra := kx_add_wrimgs segs m l2c KZS (@nil zk) in
      let zks := constr:(zks0 ++ (cp ++ extra)) in
      let ra := kx_raks l2c AKS in
      lazymatch ra with (?l2, ?aks) =>
      let r3 := kx_rrs l2 RRS in
      lazymatch r3 with (?l3, ?rs) =>
      let r4 := kx_rrs l3 WWS in
      lazymatch r4 with (?zs, ?ws) =>
      let nz := kx_len zs in
      let stops := eval vm_compute in STOPS in
      let akn := eval vm_compute in (map zak_aent aks) in
      let res := kx_trunA_fix segs VMAX akn FUEL stops SCALLS pcv rz zks (@nil kentry) rs ws nz 4%nat in
      lazymatch res with
      | ((?t, ?r, ?reads, _, ?es0), ?rk) =>
          kx_report_tree t;
          change (evtF segs RNG Q (MS (mkRl xs) F (Z_to_bv 64 pcv) fc None m rom));
          refine (kx_treeA_evtF segs F fc RNG Q VMAX FUEL stops SCALLS zs rz xs zks rk aks pcv m rom t r reads rs ws _ _ _ _ _ _ _ _);
          [ vm_cast_no_check (@eq_refl ktreeA t)
          | kx_cert
          | kx_regs_eqs
          | apply Forall_app; split; [ kxl_zks_solve | apply Forall_app; split; [ kxl_cells_solve ds | kxl_zks_solve ] ]
          | kxl_zregs_solve
          | kxl_zwins_solve
          | kxa_zaks_solve
          | let E := fresh "KXE" in let HE := fresh "KXEO" in let HK := fresh "KXK" in
            let KXA := fresh "KXA" in let KXRD := fresh "KXRD" in
            intros E HE HK; destruct HE as [KXA KXRD];
            change (reads_ok segs m nz reads E) in KXRD;
            kx_tree_splitF segs RNG Q F fc m rom E zs nz KXA rz es0 xs r ]
      end end end end end end end
  end.

Tactic Notation "kx_autoA" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in
  kx_autoA_core 0 stops (FUEL : nat) true aks kzs rrs.
Tactic Notation "kx_autoA_nocall" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in
  kx_autoA_core 0 stops (FUEL : nat) false aks kzs rrs.
Tactic Notation "kx_autoFA" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFA_core 0 stops (FUEL : nat) true aks kzs rrs wws.
Tactic Notation "kx_autoFA_nocall" uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFA_core 0 stops (FUEL : nat) false aks kzs rrs wws.
Tactic Notation "kx_autoFLA" constr(CH) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFLA_core 0 stops (FUEL : nat) true CH aks kzs rrs wws.
Tactic Notation "kx_autoFLA_nocall" constr(CH) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) uconstr(WWS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in let wws := constr:(WWS : list (Z * Z)) in
  kx_autoFLA_core 0 stops (FUEL : nat) false CH aks kzs rrs wws.
Tactic Notation "kx_autoA_v" constr(VMAX) uconstr(AKS) uconstr(STOPS) constr(FUEL) uconstr(KZS) uconstr(RRS) :=
  let stops := constr:(STOPS : list Z) in let aks := constr:(AKS : list kza) in let kzs := constr:(KZS : list kz) in
  let rrs := constr:(RRS : list (Z * Z)) in
  kx_autoA_core (VMAX : Z) stops (FUEL : nat) true aks kzs rrs.
