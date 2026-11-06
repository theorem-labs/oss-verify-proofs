(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Pm4RegionPoisoned Pm4AsanMemset Pm4AsanMemcpy Pm4StrlenIcpt Pm4TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_65000_66000 Pm4_code_66000_67000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memtoshadow47_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x66948 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret p (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
  unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
  destruct Hp as [Hlow|Hhigh].
  - eexists. split.
    + stepn F_668f8 D_668f8.                                     (* [comment removed for export] *)
      mld F_668fc D_668fc (0x160c18 : word) G1.                     (* [comment removed for export] *)
      mld F_66900 D_66900 (0x169ef8 : word) G2.                     (* [comment removed for export] *)
      stepn F_66904 D_66904.                                     (* [comment removed for export] *)
      stepn F_66908 D_66908.                                     (* [comment removed for export] *)
      stepn F_6690c D_6690c.                                     (* [comment removed for export] *)
      stepn F_66910 D_66910.                                     (* [comment removed for export] *)
      stepb_tk F_66914 D_66914 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_66958 D_66958 (Z_to_bv 64 (p / 8)) ltac:(wval).    (* [comment removed for export] *)
      stepiv F_6695c D_6695c (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).   (* [comment removed for export] *)
      stepret F_66960 D_66960 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
  - eexists. split.
    + stepn F_668f8 D_668f8.
      mld F_668fc D_668fc (0x160c18 : word) G1.
      mld F_66900 D_66900 (0x169ef8 : word) G2.
      stepn F_66904 D_66904.
      stepn F_66908 D_66908.
      stepn F_6690c D_6690c.
      stepn F_66910 D_66910.
      stepb_ft F_66914 D_66914 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_66918 D_66918.                                     (* [comment removed for export] *)
      mld F_6691c D_6691c (0x160c20 : word) G3.                     (* [comment removed for export] *)
      stepn F_66920 D_66920.                                     (* [comment removed for export] *)
      mld F_66924 D_66924 (0x160c28 : word) G5.                     (* [comment removed for export] *)
      mld F_66928 D_66928 (0x16abe8 : word) G4.                     (* [comment removed for export] *)
      mld F_6692c D_6692c (0x16abf0 : word) G6.                     (* [comment removed for export] *)
      stepn F_66930 D_66930.                                     (* [comment removed for export] *)
      stepb_tk F_66934 D_66934 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_6693c D_6693c.                                     (* [comment removed for export] *)
      mld F_66940 D_66940 (0x160c30 : word) G7.                     (* [comment removed for export] *)
      mld F_66944 D_66944 (0x16abe0 : word) G8.                     (* [comment removed for export] *)
      stepn F_66948 D_66948.                                     (* [comment removed for export] *)
      stepn F_6694c D_6694c.                                     (* [comment removed for export] *)
      stepb_ft F_66950 D_66950 ltac:(cond).                      (* [comment removed for export] *)
      stepb_ft F_66954 D_66954 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_66958 D_66958 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_6695c D_6695c (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_66960 D_66960 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_8191 : forall a, Z.land a 8191 = (a mod 8192)%Z.
Proof. intros a. change 8191%Z with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Section FSM1.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra a0v : word.
  (* [comment removed for export] *)
  Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  (* [comment removed for export] *)
  Variables fs h pos ff : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.          (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
    tls_cells tpv 0x161a38 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
  (* [comment removed for export] *)
  Hypothesis Hfs : (0x6c0000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
  Hypothesis Hpos_def : pos = (h mod 8192)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2 ^ 20 + 128 * pos)%Z.
  Definition tls_r : Z := tls_res off ent.
  Hypothesis Hr : (0 <= tls_r /\ tls_r + 8 < 2 ^ 64)%Z /\ (tls_r + 8 <= s - 208 \/ s <= tls_r)%Z /\ (tls_r + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_r)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_r) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].                     (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).   (* [comment removed for export] *)
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)). (* [comment removed for export] *)
  Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) 1%nat = Some [Z_to_bv 8 0].      (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.   (* [comment removed for export] *)
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 16%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 16 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 16 <= 0x160c18 \/ 0x16abf8 <= SB + ff / 8)%Z.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.

  (* [comment removed for export] *)
  Definition F4 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).

  (* [comment removed for export] *)
  Definition fsm1_mem (Mj : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
      (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))                 (* [comment removed for export] *)
      (Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1])                             (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))                      (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos))))   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))                   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).                (* [comment removed for export] *)

  Lemma sp_s1 : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem fsm1_run : forall regs,
    getr regs 10 = a0v -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x65fe4 : word) mem0 rom) (mkst regs' ra (fsm1_mem Mj) rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> Mj x = mem0 x) /\ mem_grows mem0 Mj.
  Proof.
    hide_dj.
    intros regs H10 H4 H2 H1. rewrite sp_s1 in H2.
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs2.
    pose proof (Z.mod_pos_bound h 8192 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Hffb : (fs + 4096 + 32768 + 2 ^ 20 <= ff /\ ff + 128 <= fs + 4096 + 32768 + 2 * 2 ^ 20)%Z) by (rewrite Hff_def; lia).
    unhide Hr. destruct Hr as (R1 & R2 & R3). hide R2. hide R3.
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x65fe4 : word) mem0 rom) (mkst r1 (0x6b99c : word) (F4 regs) rom)
              /\ (getr r1 10 = Z_to_bv 64 0x161a38 /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 2 = Z_to_bv 64 (s - 32)
                  /\ getr r1 1 = (0x66008 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
    { unfold F4. eexists. split.
      - stepiv F_65f94 D_65f94 (Z_to_bv 64 (s - 32)) ltac:(wval).                                        (* [comment removed for export] *)
        stepsd F_65f98 D_65f98 (Z_to_bv 64 (s - 8)) ra
          ltac:(apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
        stepsd F_65f9c D_65f9c (Z_to_bv 64 (s - 16)) (getr regs 8)
          ltac:(apply (store_ok_mono _ _ mem0); [apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepsd F_65fa0 D_65fa0 (Z_to_bv 64 (s - 24)) (getr regs 9)
          ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepsd F_65fa4 D_65fa4 (Z_to_bv 64 (s - 32)) (getr regs 18)
          ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; [eapply mem_grows_trans; apply wbytes_grows | apply wbytes_grows]|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepiv F_65fa8 D_65fa8 (Z_to_bv 64 s) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_65fac D_65fac.                                                                             (* [comment removed for export] *)
        stepn F_65fb0 D_65fb0.                                                                             (* [comment removed for export] *)
        stepn F_65fb4 D_65fb4.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q4 & Q8 & Q2 & Q1 & K1).
    assert (Hra : ret_ok (0x66008 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrb : ret_ok (0x6612c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (OF4 : forall x : word, (bv_unsigned x < s - 32 \/ s <= bv_unsigned x)%Z -> F4 regs x = mem0 x).
    { intros x Hx. unfold F4. pose proof (u64_range x).
      destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                             | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
    (* [comment removed for export] *)
    destruct (wrap_tls_get_addr_run (F4 regs) rom (Z_to_bv 64 (s - 32)) (0x66008 : word) (s - 32) tpv 0x161a38 md off dtv ent key tsd ctx th tb te F V verb dto blk rec
                ltac:(unorm; reflexivity) Hra ltac:(lia)
                ltac:(replace (s - 32 - 176)%Z with (s - 208)%Z by lia; apply (store_ok_mono _ _ mem0); [unfold F4; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
                      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia])
                Htp ltac:(lia) Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec
                ltac:(intros M' HM'; apply HC0; intros x Hx; rewrite (HM' x) by lia; apply OF4; lia)
                r1 Q10 Q4 Q2 Q1) as (r2 & M2 & RUN2 & T10 & T2 & T1 & K2 & O2 & G2).
    replace (s - 32 - 176)%Z with (s - 208)%Z in O2 by lia.
    fold tls_r in T10.
    assert (O2' : forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M2 x = mem0 x).
    { intros x Hx. rewrite (O2 x) by lia. apply OF4. lia. }
    assert (T8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    (* [comment removed for export] *)
    unhide R2. unhide R3. unhide Fs2.
    assert (EQ : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
                 rdn ASEGS M2 (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
    { intros a k Ha Hk1 Hk2. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O2'. lia. }
    pose proof HRfs as C0. rewrite <- (EQ tls_r 8%nat) in C0 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hng as C1. rewrite <- (EQ (fs + 96)%Z 1%nat) in C1 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hssl as C2. rewrite <- (EQ (fs + 88)%Z 8%nat) in C2 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hhint as C3. rewrite <- (EQ (fs + 8)%Z 8%nat) in C3 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hflag as C4. rewrite <- (EQ (fs + 4096 + 16384 + pos)%Z 1%nat) in C4 by (cbn [Z.of_nat Pos.to_nat]; lia).
    (* [comment removed for export] *)
    hide R3.
    assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 16 < 2 ^ 64)%Z).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
    (* [comment removed for export] *)
    assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x6c0000)%Z -> M x = mem0 x) -> rt_layout_globs M).
    { intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
      repeat split; assumption. }
    assert (G2' : mem_grows mem0 M2).
    { eapply mem_grows_trans; [|exact G2]. unfold F4. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    clear G2. rename G2' into G2.
    (* [comment removed for export] *)
    set (N1 := wbytes M2 (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1)))).
    set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1]).
    set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
    set (N4 := wbytes N3 (Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos)))).
    set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N6 := wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (GN4 : mem_grows mem0 N4) by (unfold N4, N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact G2).
    assert (WFS : forall M (a : Z) (k : nat), mem_grows mem0 M -> (fs <= a)%Z -> (a + Z.of_nat k <= fs + 4096 + 32768 + 11 * 2 ^ 20)%Z ->
                  store_ok ASEGS M (Z_to_bv 64 a) k = true).
    { intros M a k HM Ha Hk. apply (store_ok_mono _ _ mem0 M _ HM).
      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)));
        [unorm; rewrite Z2Nat.id by lia; lia | exact Hwfs | unorm; lia | unorm; rewrite Z2Nat.id by lia; lia]. }
    assert (GLN4 : rt_layout_globs N4).
    { apply GL. intros x Hx. pose proof (u64_range x). unfold N4, N3, N2, N1.
      rewrite !wbytes_below; first [apply O2'; lia | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]. }
    #[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
      try change (2 ^ 7)%Z with 128%Z; first [reflexivity | f_equal; lia].
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x66008 : word) M2 rom) (mkst r3 (0x66948 : word) N4 rom)
              /\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
                  /\ getr r3 1 = (0x6612c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
    { eexists. split.
      - chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_65fb8 | reflexivity | exact D_65fb8
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 tls_r) by (symmetry; wv2) end; exact C0 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb_ft F_65fbc D_65fbc ltac:(cond).                                                              (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_65fc0 | reflexivity | exact D_65fc0
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 96)) by (symmetry; wv2) end; exact C1] | step_simpl; vnorm].   (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_65fc4 | reflexivity | exact D_65fc4
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 88)) by (symmetry; wv2) end; exact C2 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_65fc8 D_65fc8.                                                                             (* [comment removed for export] *)
        stepn F_65fd8 D_65fd8.                                                                             (* [comment removed for export] *)
        stepn F_65fdc D_65fdc.                                                                             (* [comment removed for export] *)
        stepn F_65fe0 D_65fe0.                                                                             (* [comment removed for export] *)
        stepn F_65fe4 D_65fe4.                                                                             (* [comment removed for export] *)
        stepb F_65fe8 D_65fe8.                                                                             (* [comment removed for export] *)
        stepn F_65fec D_65fec.                                                                             (* [comment removed for export] *)
        stepn F_65ff0 D_65ff0.                                                                             (* [comment removed for export] *)
        stepn F_65ff4 D_65ff4.                                                                             (* [comment removed for export] *)
        stepn F_65ff8 D_65ff8.                                                                             (* [comment removed for export] *)
        stepn F_65ffc D_65ffc.                                                                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_66000 | reflexivity | exact D_66000
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 8)) by (symmetry; wv2) end; exact C3 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepn F_66004 D_66004.                                                                             (* [comment removed for export] *)
        stepn F_66008 D_66008.                                                                             (* [comment removed for export] *)
        stepiv F_6600c D_6600c (Z_to_bv 64 (fs + 4096)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepiv F_66010 D_66010 (Z_to_bv 64 (fs + 4096 + 16384)) ltac:(wv2).                                (* [comment removed for export] *)
        stepn F_66014 D_66014.                                                                             (* [comment removed for export] *)
        stepn F_66018 D_66018.                                                                             (* [comment removed for export] *)
        stepn F_6601c D_6601c.                                                                             (* [comment removed for export] *)
        stepiv F_66020 D_66020 (Z_to_bv 64 (h + 8191)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepiv F_66024 D_66024 (Z_to_bv 64 (h + 8192)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepov F_66028 D_66028 (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite land_8191, <- Hpos_def; reflexivity).   (* [comment removed for export] *)
        stepiv F_6602c D_6602c (Z_to_bv 64 (fs + 4096 + 16384 + pos)) ltac:(wv2).                          (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_66030 | reflexivity | exact D_66030
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 16384 + pos)) by (symmetry; wv2) end; exact C4] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_66034 D_66034.                                                                             (* [comment removed for export] *)
        stepiv F_660a0 D_660a0 (Z_to_bv 64 (h + 1)) ltac:(wv2).                                            (* [comment removed for export] *)
        stepn F_660a4 D_660a4.                                                                             (* [comment removed for export] *)
        stepn F_660a8 D_660a8.                                                                             (* [comment removed for export] *)
        stepiv F_660ac D_660ac (Z_to_bv 64 (128 * pos)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepsd F_660b0 D_660b0 (Z_to_bv 64 (fs + 8)) (Z_to_bv 64 (h + 1)) ltac:(apply WFS; [exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes M2 (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1)))) with N1.
        chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 16384 + pos)) (b := Z_to_bv 8 1);
            [exact F_660b4 | reflexivity | exact D_660b4 | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
            | apply WFS; [unfold N1; eapply mem_grows_trans; [exact G2 | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].   (* [comment removed for export] *)
        change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1]) with N2.
        stepn F_660b8 D_660b8.                                                                             (* [comment removed for export] *)
        stepn F_660bc D_660bc.                                                                             (* [comment removed for export] *)
        stepiv F_660c0 D_660c0 (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).                                (* [comment removed for export] *)
        stepiv F_660c4 D_660c4 (Z_to_bv 64 (2 ^ 20 + 128 * pos)) ltac:(wv2).                               (* [comment removed for export] *)
        stepiv F_660c8 D_660c8 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepsd F_660cc D_660cc (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
          ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
        stepsd F_660d0 D_660d0 (Z_to_bv 64 (ff + 120)) (Z_to_bv 64 (fs + 4096 + 16384 + pos))
          ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N3 (Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos)))) with N4.
        stepiv F_660d4 D_660d4 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepn F_660d8 D_660d8.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
    destruct (memtoshadow47_run r3 N4 rom (0x6612c : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
    assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
    assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
    unhide Hshadow_dj. destruct Hshadow_dj as [SD1 SD2]. unhide Fs2. unhide R2.
    (* [comment removed for export] *)
    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
                 rdn ASEGS N6 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 32)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 N6 (F4 regs)); [| unorm; cbn; lia |].
      - unfold F4. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
          apply rdn_wbytes_hit8; unorm; lia.
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
        unfold N6, N5, N4, N3, N2, N1.
        assert (OUT : forall (m : word -> option byte) (a : Z) (l : list byte), (0 <= a)%Z -> (a + Z.of_nat (length l) < 2 ^ 64)%Z ->
                   (a + Z.of_nat (length l) <= s - 208 \/ s <= a)%Z -> wbytes m (Z_to_bv 64 a) l x = m x).
        { intros m a l Ha Hl Hd. destruct Hd as [Hd|Hd].
          - apply wbytes_above. unorm. lia.
          - apply wbytes_below; unorm; lia. }
        assert (ESB : SB = 2147450880%Z) by reflexivity.
        rewrite !OUT by (first [rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; lia | lia]).
        apply O2. lia. }
    assert (ESB : SB = 2147450880%Z) by reflexivity.
    eexists. exists M2. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      stepiv F_660dc D_660dc (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_660e0 D_660e0 (Z_to_bv 64 ff) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepn F_660e4 D_660e4.                                                                              (* [comment removed for export] *)
      stepsd F_660e8 D_660e8 (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [exact GN4|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 16%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
      stepsd F_660ec D_660ec (Z_to_bv 64 (SB + ff / 8 + 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [unfold N5; eapply mem_grows_trans; [exact GN4 | apply wbytes_grows]|];
              apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 16%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N6.
      #[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; split; reflexivity].
      stepld F_660f0 D_660f0 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; slv).        (* [comment removed for export] *)
      stepld F_660f4 D_660f4 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; slv).
      stepld F_660f8 D_660f8 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; slv).
      stepld F_660fc D_660fc (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; slv).
      stepiv F_66100 D_66100 (Z_to_bv 64 s) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepret F_66104 D_66104 ra ltac:(rwH; reflexivity).
      unfold N6, N5, N4, N3, N2, N1. fold (fsm1_mem M2).
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; symmetry; apply sp_s1|]. split; [gres; reflexivity|].
      split.
      + assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
        { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|].
          eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs; exact K4. }
        intros r Hcs. destruct (decide (r = 1%bv)) as [->|N1']; [gres; rewrite H1; reflexivity|].
        destruct (decide (r = 2%bv)) as [->|N2']; [gres; rewrite H2; reflexivity|].
        destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
        destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|].
        repeat (rewrite getr_other; [| intros ->; first [match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end | cbv in Hcs; clear -Hcs; intuition discriminate]]).
        apply KB; [exact Hcs|]. clear -N1' N2' N8 N9 N18. cbv. intuition congruence.
      + split; [exact O2' | exact G2].
  Qed.
End FSM1.
End FPX_1.
