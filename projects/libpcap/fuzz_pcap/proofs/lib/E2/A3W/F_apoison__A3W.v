(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_apoison.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition poison_entry := 0x5759c%Z.

(* [comment removed for export] *)
Definition poison_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                               C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)]
  /\ rw_cells asegs m 0xa54d0 [C8 (Z_to_bv 64 0xa7360)]
  /\ rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)]
  /\ rw_cells asegs m 0xae5f8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xaf2e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xade5c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1401a0 [C8 (Z_to_bv 64 18446744073709551615)].

#[using="Type"] Lemma poison_cells_frame : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].

End CANSEC1.
Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact DST
    | assumption
    | rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition poison_core__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x575d0) fc None m1 (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 24).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 25).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 26).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 27).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 28).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 29).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 30).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 31).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 32).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 33).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 34).
Variable v : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 37).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 38).
#[using="Type"] Lemma poison_core__body : ltac:(let T := type of (fun (h : poison_core__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 addr size v lo junk fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (m1, (addr, (size, (v, (lo, (junk, fj))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  unfold ablk, AIMG_HI, KLS in HI.                     (* [comment removed for export] *)
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed.
End Zd1.
#[using="Type"] Lemma poison_core : ltac:(let t := eval cbv delta [poison_core__stmt] in poison_core__stmt in exact t).
Proof. exact poison_core__body. Qed.

#[using="Type"] Lemma poison_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try eassumption; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition poison_entry := 0x57604%Z.

(* [comment removed for export] *)
Definition poison_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                               C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)]
  /\ rw_cells asegs m 0xa58b0 [C8 (Z_to_bv 64 0xa7740)]
  /\ rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)]
  /\ rw_cells asegs m 0xae9f8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xaf6e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
  /\ rw_cells asegs m 0xae25c [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x1405a0 [C8 (Z_to_bv 64 18446744073709551615)].

#[using="Type"] Lemma poison_cells_frame : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv) W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, A + n <= AIMG_HI -> disjoint_from W A n).
  { intros A n HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold poison_cells, AIMG_HI in *.
  (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 v) (Z.to_nat (shlen size)))].

End CANSEC1.
Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact DST
    | assumption
    | rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition poison_core__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57638) fc None m1 (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 24).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 25).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 26).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 27).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 28).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 29).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 30).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 31).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 32).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 33).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 34).
Variable v : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 37).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'poison_core__stmt 38).
#[using="Type"] Lemma poison_core__body : ltac:(let T := type of (fun (h : poison_core__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 addr size v lo junk fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (m1, (addr, (size, (v, (lo, (junk, fj))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  unfold ablk, AIMG_HI, KLS in HI.                     (* [comment removed for export] *)
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed.
End Zd1.
#[using="Type"] Lemma poison_core : ltac:(let t := eval cbv delta [poison_core__stmt] in poison_core__stmt in exact t).
Proof. exact poison_core__body. Qed.

#[using="Type"] Lemma poison_shadow_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try eassumption; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed.
End CANSEC2.
End TwB.
End F_apoison.

(* [comment removed for export] *)
Module APoisonR_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition PZR_STACK : Z := 592.

(* [comment removed for export] *)
Definition premap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)]                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)]                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401b8 [C8 (Z_to_bv 64 0)]                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140200 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140218 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]   (* [comment removed for export] *)
  /\ (exists cb : list byte, rw_cells asegs m 0x6015f8 [CB 8 cb])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601878 [C8 (Z_to_bv 64 4096)].                    (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
#[using="Type"] Lemma premap_word_212a00 : forall m,
  rw_cells asegs m 0x140200 [C8 (Z_to_bv 64 0x10101000100)] ->
  rw_cells asegs m 0x140200 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.
#[using="Type"] Lemma premap_word_212a18 : forall m,
  rw_cells asegs m 0x140218 [C8 (Z_to_bv 64 0x101000100000000)] ->
  rw_cells asegs m 0x140218 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition premap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ (fp_bw RNG -> fp_bw RNG')      (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono asegs m m'
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]     (* [comment removed for export] *)
  /\ rng RNG' (shad addr) (shlen size)
  /\ poison_cells m' /\ premap_cells m'.

Definition poison_remap_stmt : Prop :=
  forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0x10000 <= shlen size ->                                     (* [comment removed for export] *)
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (* [comment removed for export] *)
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      premap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition PZR_STACK : Z := 592.

(* [comment removed for export] *)
Definition premap_cells (m : amem) : Prop :=
     rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)]                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)]                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405b8 [C8 (Z_to_bv 64 0)]                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140600 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140618 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                               C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]   (* [comment removed for export] *)
  /\ (exists cb : list byte, rw_cells asegs m 0x6019f8 [CB 8 cb])        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601c78 [C8 (Z_to_bv 64 4096)].                    (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
#[using="Type"] Lemma premap_word_212a00 : forall m,
  rw_cells asegs m 0x140600 [C8 (Z_to_bv 64 0x10101000100)] ->
  rw_cells asegs m 0x140600 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.
#[using="Type"] Lemma premap_word_212a18 : forall m,
  rw_cells asegs m 0x140618 [C8 (Z_to_bv 64 0x101000100000000)] ->
  rw_cells asegs m 0x140618 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
                            C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Proof. intros m H. eapply rw_cells_recast; [exact H| cbn; tauto| apply bytes_eq_of_unsigned; vm_compute; reflexivity| reflexivity]. Qed.

(* [comment removed for export] *)
Definition premap_post (RNG : footprint) (sp : word) (addr size lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : Prop :=
     fp_le RNG RNG' /\ (fp_bw RNG -> fp_bw RNG')      (* [comment removed for export] *)
  /\ munch [(bv_unsigned sp - PZR_STACK, bv_unsigned sp); (shad addr, shad addr + shlen size)] m m' /\ wmono asegs m m'
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat (shlen size)) (zeros (shlen size))]     (* [comment removed for export] *)
  /\ rng RNG' (shad addr) (shlen size)
  /\ poison_cells m' /\ premap_cells m'.

Definition poison_remap_stmt : Prop :=
  forall (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (addr size lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PZR_STACK ->
  mem_inv asegs m ->
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0x10000 <= shlen size ->                                     (* [comment removed for export] *)
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  (* [comment removed for export] *)
  (forall RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      premap_post RNG sp addr size lo m RNG' m' ->
      implS asegs RNG' (aembed ATOP k) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 addr size k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
End CANSEC1.
End TwB.
End APoisonR_iface.

(* [comment removed for export] *)
Module F_apoison0.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact DST
    | assumption
    | rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition poison_core0__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x575d0) fc None m1 (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 24).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 25).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 26).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 27).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 28).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 29).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 30).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 31).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 32).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 33).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 34).
Variable v : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 37).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 38).
#[using="Type"] Lemma poison_core0__body : ltac:(let T := type of (fun (h : poison_core0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 addr size v lo junk fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (m1, (addr, (size, (v, (lo, (junk, fj))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed.
End Zd1.
#[using="Type"] Lemma poison_core0 : ltac:(let t := eval cbv delta [poison_core0__stmt] in poison_core0__stmt in exact t).
Proof. exact poison_core0__body. Qed.

#[using="Type"] Lemma poison_shadow_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8600 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core0 RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try eassumption; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_post_k (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr k v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + k)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))].

#[using="Type"] Lemma poison_shadow_spec_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RTLS RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec; eassumption.
Qed.

#[using="Type"] Lemma poison_shadow_spec0_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RTLS RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec0; eassumption.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac poison_tail sp v MU WM DST RSH FR ST :=
  do 3 step; do 8 step; step;
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact DST
    | assumption
    | rewrite !unsigned_lit by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]); exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in let MU2 := fresh "MU2" in let WM2 := fresh "WM2" in
  let MI2 := fresh "MI2" in let DST2 := fresh "DST2" in let FR' := fresh "FR'" in let ST' := fresh "ST'" in
  intros ms' PO; unfold memset_post in PO; unfold poison_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by (first [ solve [unfold shlen; rewrite ?Z.shiftr_div_pow2 by lia; lia] | unfold shlen in *; rewrite ?Z.shiftr_div_pow2 in * by lia; Z.div_mod_to_equations; lia ]);
  rewrite ?unsigned_lit in DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia; change (0 mod 256) with 0 in DST2;
  do 16 eexists; split; [reflexivity|];
  split; [eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; let xq := fresh in let Hxq := fresh in intros xq Hxq; cbn in Hxq |- *; tauto |];
  split; [eapply wmono_trans; [exact WM| exact WM2] |]; split; [exact MI2|];
  split; [| exact DST2];
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR';
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST';
  eapply stk_release in FR'; [| exact ST' | lia]; cbn [cells_size csize Nat.add] in FR';
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end; exact FR'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition poison_core0__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m m1 : amem) (addr size v lo : Z) (junk fj : list byte),
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m1 ->
  poison_cells m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [CB 8 fj; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m m1 -> wmono asegs m m1 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m1 (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57638) fc None m1 (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 9).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 10).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 11).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 12).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 13).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 14).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 15).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 16).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 19).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 20).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 21).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 22).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 23).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 24).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 25).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 26).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 27).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 28).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 29).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 30).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 31).
Variable m1 : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 32).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 33).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 34).
Variable v : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 35).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 36).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 37).
Variable fj : ltac2:(SecDietF.SzSecF.ty 'poison_core0__stmt 38).
#[using="Type"] Lemma poison_core0__body : ltac:(let T := type of (fun (h : poison_core0__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m m1 addr size v lo junk fj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (m1, (addr, (size, (v, (lo, (junk, fj))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO MI PC FR MU WM AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  zstep. step. if_cases K1; zify_cond K1.               (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 step.                                           (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  step. if_cases K2; zify_cond K2.                     (* [comment removed for export] *)
  2: do 6 step.                                        (* [comment removed for export] *)
  2: zstep; step; if_cases K3; zify_cond K3; [| exfalso; lia].   (* [comment removed for export] *)
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K4; zify_cond K4; [exfalso; lia|].           (* [comment removed for export] *)
  2: step; if_cases K5; zify_cond K5; [| exfalso; lia].          (* [comment removed for export] *)
  2: step; do 2 zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K6; zify_cond K6; [exfalso; lia|].
  2: step; if_cases K7; zify_cond K7; [| exfalso; lia].          (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: zstep; step; if_cases K8; zify_cond K8;
       [ exfalso; apply K8; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2^3) with 8; exact SL |].
  all: do 2 zstep.                                     (* [comment removed for export] *)
  all: step; if_cases K9; zify_cond K9.                (* [comment removed for export] *)
  all: try (exfalso; lia).
  (* [comment removed for export] *)
  2: do 6 step; zstep.                                 (* [comment removed for export] *)
  2: step; if_cases K10; zify_cond K10; [| exfalso; lia].
  2: do 3 step; do 2 zstep.                            (* [comment removed for export] *)
  2: step; if_cases K11; zify_cond K11; [exfalso; lia|].
  2: step; if_cases K12; zify_cond K12; [exfalso; lia|].
  (* [comment removed for export] *)
  all: do 3 step.                                      (* [comment removed for export] *)
  all: step; if_lit.                                   (* [comment removed for export] *)
  all: do 5 zstep.                                     (* [comment removed for export] *)
  all: replace ((Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3) with (shlen size)
      by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
  all: change (2147450880 + Z.shiftr addr 3) with (shad addr).
  (* [comment removed for export] *)
  all: step; if_cases KV; zify_cond KV;
      [| do 2 step; lstep; step; if_cases KT; zify_cond KT;
         [| exfalso; rewrite ?Z.mod_small in KT by (unfold shlen; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia); lia]].
  (* [comment removed for export] *)
  all: poison_tail sp v MU WM DST RSH FR ST.
Qed.
End Zd1.
#[using="Type"] Lemma poison_core0 : ltac:(let t := eval cbv delta [poison_core0__stmt] in poison_core0__stmt in exact t).
Proof. exact poison_core0__body. Qed.

#[using="Type"] Lemma poison_shadow_spec0 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat (shlen size)) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) (shlen size) ->
  evtF asegs RNG (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC -> -> -> AL SL SZ HI HE V V0 DST RIMG RTLS RSTK RSH.
  atop_facts. pose proof PC as PC'. (nd_pre PC' 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + shlen size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof HI as HI'. unfold ablk, AIMG_HI, KLS in HI'.
  assert (SHR : 0x800b8800 <= shad addr /\ shad addr + shlen size <= 0x10007fff8000 /\ 0 <= shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  word_range sp SPR.
  carve_frame 64%nat ST.
  do 8 step.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. if_cases KV; zify_cond KV.
  2: step; lstep; step; step; if_lit.                  (* [comment removed for export] *)
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         eapply (poison_core0 RNG ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mm addr size v lo junk) end.
  all: try eassumption; try lia.
  all: eapply poison_cells_frame; [exact PC | exact MU | exact WM | ].
  all: apply Forall_cons; [cbn; unfold AIMG_HI; lia|]; apply Forall_cons; [cbn; unfold AIMG_HI; lia | apply Forall_nil].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_post_k (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr k v lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shad addr, shad addr + k)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (shad addr) [CB (Z.to_nat k) (repeat (Z_to_bv 8 v) (Z.to_nat k))].

#[using="Type"] Lemma poison_shadow_spec_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> ablk addr (addr + size) -> addr + size <= 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RTLS RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec; eassumption.
Qed.

#[using="Type"] Lemma poison_shadow_spec0_k : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (addr size k v lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  poison_cells m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 v ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 <= size -> ablk (addr - 8) (addr + size) -> addr + size < 2^47 ->     (* [comment removed for export] *)
  0 <= v < 256 -> (v = 0 -> shlen size < 18446744073709551615) -> shlen size = k ->
  rw_cells asegs m (shad addr) [CB (Z.to_nat k) junk] ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad addr) k ->
  evtF asegs RNG (poison_post_k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr k v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros ST CEIL LO MI PC Ha0 Ha1 Ha2 AL SL SZ HI HE V V0 HK DST RIMG RTLS RSTK RSH. subst k.
  unfold poison_post_k. eapply poison_shadow_spec0; eassumption.
Qed.
End CANSEC1.
End TwB.
End F_apoison0.

(* [comment removed for export] *)
Module F_asetshadow.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ASETSHADOW00 : Z := 0x58268.
Definition ASETSHADOWF8 : Z := 0x58388.

(* [comment removed for export] *)
Definition set_shadow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n v : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].

Local Ltac to_memset A n v DST RSH :=
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by lia; exact DST | assumption | rewrite !unsigned_lit by lia; exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; unfold memset_post in PO; unfold set_shadow_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia;
  do 15 eexists; split; [reflexivity|]; split; [exact MU2|]; split; [exact WM2|]; split; [exact MI2| exact DST2].

#[using="Type"] Lemma set_shadow_00_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (A n : Z) (junk : list byte),
  mem_inv asegs m -> poison_cells m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 < A -> 0 < n ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  rng_aimg RNG -> rng RNG A n ->
  evtF asegs RNG (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASETSHADOW00) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI PC -> -> A0 N0 DST RIMG RSH.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post). unfold ASETSHADOW00.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  step.                                                (* [comment removed for export] *)
  do 3 step.                                           (* [comment removed for export] *)
  step. step.                                          (* [comment removed for export] *)
  to_memset A n 0 DST RSH.
Qed.

#[using="Type"] Lemma set_shadow_f8_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (A n : Z) (junk : list byte),
  mem_inv asegs m -> poison_cells m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 < A -> 0 < n ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  rng_aimg RNG -> rng RNG A n ->
  evtF asegs RNG (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n 248 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASETSHADOWF8) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI PC -> -> A0 N0 DST RIMG RSH.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post). unfold ASETSHADOWF8.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  do 3 step.                                           (* [comment removed for export] *)
  step. step. step.                                    (* [comment removed for export] *)
  to_memset A n 248 DST RSH.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ASETSHADOW00 : Z := 0x582d0.
Definition ASETSHADOWF8 : Z := 0x583f0.

(* [comment removed for export] *)
Definition set_shadow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A n v : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(A, A + n)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n))].

Local Ltac to_memset A n v DST RSH :=
  eapply evtF_mono;
  [ eapply memset_spec;
    [ rewrite !unsigned_lit by lia; exact DST | assumption | rewrite !unsigned_lit by lia; exact RSH ]
  | ];
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; unfold memset_post in PO; unfold set_shadow_post; destruct_exs PO;
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post);
  rewrite !unsigned_lit in MU2, DST2 by lia; rewrite ?(Z.mod_small v 256) in DST2 by lia;
  do 15 eexists; split; [reflexivity|]; split; [exact MU2|]; split; [exact WM2|]; split; [exact MI2| exact DST2].

#[using="Type"] Lemma set_shadow_00_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (A n : Z) (junk : list byte),
  mem_inv asegs m -> poison_cells m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 < A -> 0 < n ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  rng_aimg RNG -> rng RNG A n ->
  evtF asegs RNG (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASETSHADOW00) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI PC -> -> A0 N0 DST RIMG RSH.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post). unfold ASETSHADOW00.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  step.                                                (* [comment removed for export] *)
  do 3 step.                                           (* [comment removed for export] *)
  step. step.                                          (* [comment removed for export] *)
  to_memset A n 0 DST RSH.
Qed.

#[using="Type"] Lemma set_shadow_f8_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (A n : Z) (junk : list byte),
  mem_inv asegs m -> poison_cells m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 < A -> 0 < n ->
  rw_cells asegs m A [CB (Z.to_nat n) junk] ->
  rng_aimg RNG -> rng RNG A n ->
  evtF asegs RNG (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n 248 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASETSHADOWF8) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros MI PC -> -> A0 N0 DST RIMG RSH.
  (nd_pre PC 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post). unfold ASETSHADOWF8.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B. rewrite Nat.add_0_r, Z2Nat.id in B by lia.
  do 3 step.                                           (* [comment removed for export] *)
  step. step. step.                                    (* [comment removed for export] *)
  to_memset A n 248 DST RSH.
Qed.
End CANSEC1.
End TwB.
End F_asetshadow.

(* [comment removed for export] *)
Module AFake_free7.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg RtCells AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_m2s_b__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition ASTKFREE7 : Z := 0x3f6f8.
Definition SF7_STACK : Z := 96.      (* [comment removed for export] *)

Definition sf7_W (sp flag F size : Z) : list (Z * Z) :=
  [(sp - SF7_STACK, sp); (flag, flag + 1); (shad F, shad F + shlen size)].

Definition sf7_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo flag F size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf7_W (bv_unsigned sp) flag F size) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 245) (Z.to_nat (shlen size)))].

#[using="Type"] Lemma stack_free7_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo flag F size : Z) (fb : byte) (shj : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - SF7_STACK -> ATOP <= lo ->
  a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 size ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 flag)] -> rw_cells asegs m flag [C1 fb] ->
  F mod 8 = 0 -> size mod 8 = 0 -> 0 < size <= 8192 -> ablk F (F + 8192) -> F + 8192 <= ATOP ->      (* [comment removed for export] *)
  rw_cells asegs m (shad F) [CB (Z.to_nat (shlen size)) shj] ->
  ablk flag (flag + 1) -> flag + 1 <= ATOP ->
  (flag + 1 <= F \/ F + 8192 <= flag) -> (flag + 1 <= shad F \/ shad F + shlen size <= flag) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (F + 8184) 8 -> rng RNG flag 1 -> rng RNG (shad F) (shlen size) ->
  evtF asegs RNG (sf7_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo flag F size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs)).
Proof.
  intros until shj.
  intros MI ST LO CEIL -> -> PC SFP FLG FAL SAL SPOS FLO FHI SHJ FL0 FL1 FFR FSH RIMG RTLS RSTK RSFP RFLG RSH.
  (pose proof (ablk_lin _ _ FL0) as ndP__; nd_pre ndP__ 4%nat; intros FGL1 _ _ _; nd_post). unfold AIMG_HI in FGL1.
  pose proof PC as PC0. (nd_pre PC0 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.
  pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR.
  assert (FLOS : ablk F (F + size)) by (eapply ablk_sub; [exact FLO | clear; lia | clear -SPOS; lia]).
  assert (FHI47 : F + size <= 2^47) by (clear -FHI SPOS ATR; lia).
  unfold ASTKFREE7, SF7_STACK in *. word_range sp SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl (sf7_W (bv_unsigned sp) flag F size) m) as MU. unfold sf7_W, SF7_STACK in MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x800b8600 <= shad F /\ shad F + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -FAL SAL SPOS FLOB FHI ATR. Z.div_mod_to_equations. lia. }
  carve_frame 32%nat ST.
  do 4 step.                                           (* [comment removed for export] *)
  step. step.                                          (* [comment removed for export] *)
  step. zstep.                                         (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step. call m2sb_spec;
    first [ eassumption
          | (rewrite unsigned_lit by (clear -FLOL FHI SPOS; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; clear - FLOB FHI SPOS; lia)
          | idtac ].
  step. step. step.                                    (* [comment removed for export] *)
  do 4 step.                                           (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.                                                (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (poison_shadow_spec RNG) with (addr := F) (size := size) (v := 245) (lo := lo) (m := mm) end;
      try eassumption; try reflexivity.
    all: try (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split | |- rt_got _ => assumption | |- rt_real_mem _ => assumption | |- rt_shbase _ => assumption | |- rt_layout _ => assumption end)).
    all: try (clear -LO CEIL LO0 SPR SPOS; lia).
    all: try (intros EV; exfalso; clear -EV; lia). }
  intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
  unfold sf7_cpost, sf7_W, SF7_STACK. do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [eapply wmono_trans; [exact WM| exact WMp]|]. split; [exact MIp|]. split; [exact STp|].
  split; [| exact SHZ].
  eapply rw_cells_transport; [eassumption | exact MUp | exact WMp |].
  cbn [disjoint_from cells_size csize Nat.add]. clear -FSH FGL1 FL1 LO CEIL SPR. lia.
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_m2s_b__A3W.F_m2s_b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition ASTKFREE7 : Z := 0x3f760.
Definition SF7_STACK : Z := 96.      (* [comment removed for export] *)

Definition sf7_W (sp flag F size : Z) : list (Z * Z) :=
  [(sp - SF7_STACK, sp); (flag, flag + 1); (shad F, shad F + shlen size)].

Definition sf7_cpost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (lo flag F size : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (sf7_W (bv_unsigned sp) flag F size) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' flag [C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs m' (shad F) [CB (Z.to_nat (shlen size)) (repeat (Z_to_bv 8 245) (Z.to_nat (shlen size)))].

#[using="Type"] Lemma stack_free7_cspec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (FR : bvmap 5 word) fc (m : amem) (lo flag F size : Z) (fb : byte) (shj : list byte),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - SF7_STACK -> ATOP <= lo ->
  a0 = Z_to_bv 64 F -> a1 = Z_to_bv 64 size ->
  poison_cells m ->
  (* [comment removed for export] *)
  rw_cells asegs m (F + 8184) [C8 (Z_to_bv 64 flag)] -> rw_cells asegs m flag [C1 fb] ->
  F mod 8 = 0 -> size mod 8 = 0 -> 0 < size <= 8192 -> ablk F (F + 8192) -> F + 8192 <= ATOP ->      (* [comment removed for export] *)
  rw_cells asegs m (shad F) [CB (Z.to_nat (shlen size)) shj] ->
  ablk flag (flag + 1) -> flag + 1 <= ATOP ->
  (flag + 1 <= F \/ F + 8192 <= flag) -> (flag + 1 <= shad F \/ shad F + shlen size <= flag) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (F + 8184) 8 -> rng RNG flag 1 -> rng RNG (shad F) (shlen size) ->
  evtF asegs RNG (sf7_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo flag F size m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 ASTKFREE7) fc None m (seg_rom asegs)).
Proof.
  intros until shj.
  intros MI ST LO CEIL -> -> PC SFP FLG FAL SAL SPOS FLO FHI SHJ FL0 FL1 FFR FSH RIMG RTLS RSTK RSFP RFLG RSH.
  (pose proof (ablk_lin _ _ FL0) as ndP__; nd_pre ndP__ 4%nat; intros FGL1 _ _ _; nd_post). unfold AIMG_HI in FGL1.
  pose proof PC as PC0. (nd_pre PC0 7%nat; intros GOT GOTMS REAL SHB LAY CANP THR; nd_post).
  (pose proof (ablk_lin _ _ FLO) as ndP__; nd_pre ndP__ 4%nat; intros FLOL _ _ _; nd_post). unfold AIMG_HI in FLOL.
  pose proof FLO as FLOB. unfold ablk, AIMG_HI, KLS in FLOB. pose proof atop_range as ATR.
  assert (FLOS : ablk F (F + size)) by (eapply ablk_sub; [exact FLO | clear; lia | clear -SPOS; lia]).
  assert (FHI47 : F + size <= 2^47) by (clear -FHI SPOS ATR; lia).
  unfold ASTKFREE7, SF7_STACK in *. word_range sp SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl (sf7_W (bv_unsigned sp) flag F size) m) as MU. unfold sf7_W, SF7_STACK in MU. pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x800b8800 <= shad F /\ shad F + shlen size <= 0x10007fff8000 /\ 0 < shlen size).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear -FAL SAL SPOS FLOB FHI ATR. Z.div_mod_to_equations. lia. }
  carve_frame 32%nat ST.
  do 4 step.                                           (* [comment removed for export] *)
  step. step.                                          (* [comment removed for export] *)
  step. zstep.                                         (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step.                                                (* [comment removed for export] *)
  step. call m2sb_spec;
    first [ eassumption
          | (rewrite unsigned_lit by (clear -FLOL FHI SPOS; lia); unfold KLOW, KHIGH, KEND;
             destruct FLOB as [FLOB|FLOB]; [left|right]; clear - FLOB FHI SPOS; lia)
          | idtac ].
  step. step. step.                                    (* [comment removed for export] *)
  do 4 step.                                           (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -32) _ |- _ =>
    lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
  step.                                                (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (poison_shadow_spec RNG) with (addr := F) (size := size) (v := 245) (lo := lo) (m := mm) end;
      try eassumption; try reflexivity.
    all: try (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split | |- rt_got _ => assumption | |- rt_real_mem _ => assumption | |- rt_shbase _ => assumption | |- rt_layout _ => assumption end)).
    all: try (clear -LO CEIL LO0 SPR SPOS; lia).
    all: try (intros EV; exfalso; clear -EV; lia). }
  intros ms' PO. unfold poison_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUp WMp MIp STp SHZ; nd_post).
  unfold sf7_cpost, sf7_W, SF7_STACK. do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUp]. intros xq Hq. cbn in Hq |- *. clear -Hq. lia. }
  split; [eapply wmono_trans; [exact WM| exact WMp]|]. split; [exact MIp|]. split; [exact STp|].
  split; [| exact SHZ].
  eapply rw_cells_transport; [eassumption | exact MUp | exact WMp |].
  cbn [disjoint_from cells_size csize Nat.add]. clear -FSH FGL1 FL1 LO CEIL SPR. lia.
Qed.
End CANSEC1.
End TwB.
End AFake_free7.
