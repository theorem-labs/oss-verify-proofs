(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib As0RegionPoisoned As0AsanMemset As0AsanMemcpy As0StrlenIcpt As0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_4856c_48efc As0_code_4dc10_4dc14 As0FakeStack1.
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

Lemma land_mask2 : forall a, Z.land a 4095 = (a mod 4096)%Z.
Proof. intros a. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Section FSM2.
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
    tls_cells tpv 0xd6670 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
  (* [comment removed for export] *)
  Hypothesis Hfs : (0x633000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
  Hypothesis Hpos_def : pos = (h mod 4096)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2097152 + 256 * pos)%Z.
  Definition tls_rc : Z := tls_res off ent.
  Hypothesis Hr : (0 <= tls_rc /\ tls_rc + 8 < 2 ^ 64)%Z /\ (tls_rc + 8 <= s - 208 \/ s <= tls_rc)%Z /\ (tls_rc + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_rc)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_rc) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].                     (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).   (* [comment removed for export] *)
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)). (* [comment removed for export] *)
  Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 24576 + pos)) 1%nat = Some [Z_to_bv 8 0].      (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.   (* [comment removed for export] *)
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 32%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 32 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 32 <= 0xd58b8 \/ 0xde838 <= SB + ff / 8)%Z.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.

  (* [comment removed for export] *)
  Definition F4c (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).

  (* [comment removed for export] *)
  Definition fsm2_mem (Mj : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
      (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))
      (Z_to_bv 64 (fs + 4096 + 24576 + pos)) [Z_to_bv 8 1])
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (ff + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 24576 + pos))))
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  Lemma sp_sc : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem fsm2_run : forall regs,
    getr regs 10 = a0v -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' Mj,
      msteps ASEGS (mkst regs (0x48b48 : word) mem0 rom) (mkst regs' ra (fsm2_mem Mj) rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> Mj x = mem0 x) /\ mem_grows mem0 Mj.
  Proof.
    hide_dj.
    intros regs H10 H4 H2 H1. rewrite sp_sc in H2.
    unhide Hfs. destruct Hfs as (Fs1 & Fs2 & Fs3). hide Fs2.
    pose proof (Z.mod_pos_bound h 4096 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Hffb : (fs + 4096 + 32768 + 2 ^ 20 <= ff /\ ff + 256 <= fs + 4096 + 32768 + 3145728)%Z) by (rewrite Hff_def; lia).
    unhide Hr. destruct Hr as (R1 & R2 & R3). hide R2. hide R3.
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x48b48 : word) mem0 rom) (mkst r1 (0x4dc10 : word) (F4c regs) rom)
              /\ (getr r1 10 = Z_to_bv 64 0xd6670 /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 2 = Z_to_bv 64 (s - 32)
                  /\ getr r1 1 = (0x48b6c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
    { unfold F4c. eexists. split.
      - stepiv F_48b48 D_48b48 (Z_to_bv 64 (s - 32)) ltac:(wval).                                        (* [comment removed for export] *)
        stepsd F_48b4c D_48b4c (Z_to_bv 64 (s - 8)) ra
          ltac:(apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
        stepsd F_48b50 D_48b50 (Z_to_bv 64 (s - 16)) (getr regs 8)
          ltac:(apply (store_ok_mono _ _ mem0); [apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepsd F_48b54 D_48b54 (Z_to_bv 64 (s - 24)) (getr regs 9)
          ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; apply wbytes_grows|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepsd F_48b58 D_48b58 (Z_to_bv 64 (s - 32)) (getr regs 18)
          ltac:(apply (store_ok_mono _ _ mem0); [eapply mem_grows_trans; [eapply mem_grows_trans; apply wbytes_grows | apply wbytes_grows]|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
        stepiv F_48b5c D_48b5c (Z_to_bv 64 s) ltac:(wval).                                               (* [comment removed for export] *)
        stepn F_48b60 D_48b60.                                                                             (* [comment removed for export] *)
        stepn F_48b64 D_48b64.                                                                             (* [comment removed for export] *)
        stepn F_48b68 D_48b68.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q4 & Q8 & Q2 & Q1 & K1).
    assert (Hra : ret_ok (0x48b6c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (Hrb : ret_ok (0x48c94 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (OF4 : forall x : word, (bv_unsigned x < s - 32 \/ s <= bv_unsigned x)%Z -> F4c regs x = mem0 x).
    { intros x Hx. unfold F4c. pose proof (u64_range x).
      destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
                             | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
    (* [comment removed for export] *)
    destruct (wrap_tls_get_addr_run (F4c regs) rom (Z_to_bv 64 (s - 32)) (0x48b6c : word) (s - 32) tpv 0xd6670 md off dtv ent key tsd ctx th tb te F V verb dto blk rec
                ltac:(unorm; reflexivity) Hra ltac:(lia)
                ltac:(replace (s - 32 - 176)%Z with (s - 208)%Z by lia; apply (store_ok_mono _ _ mem0); [unfold F4c; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
                      apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 208)) _ 208%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia])
                Htp ltac:(lia) Hmd Hoff Hdtv Hent Hkey Htsd Hctx Hth Htbe HF HV Hverb Hdto Hblk Hrec
                ltac:(intros M' HM'; apply HC0; intros x Hx; rewrite (HM' x) by lia; apply OF4; lia)
                r1 Q10 Q4 Q2 Q1) as (r2 & M2 & RUN2 & T10 & T2 & T1 & K2 & O2 & G2).
    replace (s - 32 - 176)%Z with (s - 208)%Z in O2 by lia.
    fold tls_rc in T10.
    assert (O2' : forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M2 x = mem0 x).
    { intros x Hx. rewrite (O2 x) by lia. apply OF4. lia. }
    assert (T8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    (* [comment removed for export] *)
    unhide R2. unhide R3. unhide Fs2.
    assert (EQ : forall (a : Z) (k : nat), (0 <= a)%Z -> (a + Z.of_nat k < 2 ^ 64)%Z -> (a + Z.of_nat k <= s - 208 \/ s <= a)%Z ->
                 rdn ASEGS M2 (Z_to_bv 64 a) k = rdn ASEGS mem0 (Z_to_bv 64 a) k).
    { intros a k Ha Hk1 Hk2. apply rdn_ext; [unorm; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply O2'. lia. }
    pose proof HRfs as C0. rewrite <- (EQ tls_rc 8%nat) in C0 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hng as C1. rewrite <- (EQ (fs + 96)%Z 1%nat) in C1 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hssl as C2. rewrite <- (EQ (fs + 88)%Z 8%nat) in C2 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hhint as C3. rewrite <- (EQ (fs + 16)%Z 8%nat) in C3 by (cbn [Z.of_nat Pos.to_nat]; lia).
    pose proof Hflag as C4. rewrite <- (EQ (fs + 4096 + 24576 + pos)%Z 1%nat) in C4 by (cbn [Z.of_nat Pos.to_nat]; lia).
    (* [comment removed for export] *)
    hide R3.
    assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 32 < 2 ^ 64)%Z).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
    (* [comment removed for export] *)
    assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x633000)%Z -> M x = mem0 x) -> rt_layout_globs M).
    { intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M mem0) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
      repeat split; assumption. }
    assert (G2' : mem_grows mem0 M2).
    { eapply mem_grows_trans; [|exact G2]. unfold F4c. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    clear G2. rename G2' into G2.
    (* [comment removed for export] *)
    set (N1 := wbytes M2 (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1)))).
    set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 24576 + pos)) [Z_to_bv 8 1]).
    set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
    set (N4 := wbytes N3 (Z_to_bv 64 (ff + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 24576 + pos)))).
    set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N6 := wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N7 := wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N8 := wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
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
      try change (2 ^ 8)%Z with 256%Z; first [reflexivity | f_equal; lia].
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x48b6c : word) M2 rom) (mkst r3 (0x48e90 : word) N4 rom)
              /\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
                  /\ getr r3 1 = (0x48c94 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
    { eexists. split.
      - chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_48b6c | reflexivity | exact D_48b6c
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 tls_rc) by (symmetry; wv2) end; exact C0 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb_ft F_48b70 D_48b70 ltac:(cond).                                                              (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_48b74 | reflexivity | exact D_48b74
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 96)) by (symmetry; wv2) end; exact C1] | step_simpl; vnorm].   (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_48b78 | reflexivity | exact D_48b78
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 88)) by (symmetry; wv2) end; exact C2 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_48b7c D_48b7c.                                                                             (* [comment removed for export] *)
        stepn F_48b8c D_48b8c.                                                                             (* [comment removed for export] *)
        stepn F_48b90 D_48b90.                                                                             (* [comment removed for export] *)
        stepn F_48b94 D_48b94.                                                                             (* [comment removed for export] *)
        stepn F_48b98 D_48b98.                                                                             (* [comment removed for export] *)
        stepb F_48b9c D_48b9c.                                                                             (* [comment removed for export] *)
        stepn F_48ba0 D_48ba0.                                                                             (* [comment removed for export] *)
        stepn F_48ba4 D_48ba4.                                                                             (* [comment removed for export] *)
        stepn F_48ba8 D_48ba8.                                                                             (* [comment removed for export] *)
        stepn F_48bac D_48bac.                                                                             (* [comment removed for export] *)
        stepn F_48bb0 D_48bb0.                                                                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_48bb4 | reflexivity | exact D_48bb4
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 16)) by (symmetry; wv2) end; exact C3 | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepn F_48bb8 D_48bb8.                                                                             (* [comment removed for export] *)
        stepn F_48bbc D_48bbc.                                                                             (* [comment removed for export] *)
        stepiv F_48bc0 D_48bc0 (Z_to_bv 64 (fs + 4096)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepiv F_48bc4 D_48bc4 (Z_to_bv 64 (fs + 4096 + 24576)) ltac:(wv2).                                (* [comment removed for export] *)
        stepn F_48bc8 D_48bc8.                                                                             (* [comment removed for export] *)
        stepn F_48bcc D_48bcc.                                                                             (* [comment removed for export] *)
        stepn F_48bd0 D_48bd0.                                                                             (* [comment removed for export] *)
        stepiv F_48bd4 D_48bd4 (Z_to_bv 64 (h + 4095)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepiv F_48bd8 D_48bd8 (Z_to_bv 64 (h + 4096)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepov F_48bdc D_48bdc (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; unorm; rewrite land_mask2, <- Hpos_def; reflexivity).   (* [comment removed for export] *)
        stepiv F_48be0 D_48be0 (Z_to_bv 64 (fs + 4096 + 24576 + pos)) ltac:(wv2).                          (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_48be4 | reflexivity | exact D_48be4
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 24576 + pos)) by (symmetry; wv2) end; exact C4] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_48be8 D_48be8.                                                                             (* [comment removed for export] *)
        stepiv F_48c54 D_48c54 (Z_to_bv 64 (h + 1)) ltac:(wv2).                                            (* [comment removed for export] *)
        stepn F_48c58 D_48c58.                                                                             (* [comment removed for export] *)
        stepn F_48c5c D_48c5c.                                                                             (* [comment removed for export] *)
        stepsd F_48c60 D_48c60 (Z_to_bv 64 (fs + 16)) (Z_to_bv 64 (h + 1)) ltac:(apply WFS; [exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes M2 (Z_to_bv 64 (fs + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1)))) with N1.
        chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 24576 + pos)) (b := Z_to_bv 8 1);
            [exact F_48c64 | reflexivity | exact D_48c64 | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
            | apply WFS; [unfold N1; eapply mem_grows_trans; [exact G2 | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].   (* [comment removed for export] *)
        change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 24576 + pos)) [Z_to_bv 8 1]) with N2.
        stepn F_48c68 D_48c68.                                                                             (* [comment removed for export] *)
        stepn F_48c6c D_48c6c.                                                                             (* [comment removed for export] *)
        stepiv F_48c70 D_48c70 (Z_to_bv 64 (256 * pos)) ltac:(wv2).                                       (* [comment removed for export] *)
        stepn F_48c74 D_48c74.                                                                             (* [comment removed for export] *)
        stepiv F_48c78 D_48c78 (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).                                (* [comment removed for export] *)
        stepiv F_48c7c D_48c7c (Z_to_bv 64 (2097152 + 256 * pos)) ltac:(wv2).                             (* [comment removed for export] *)
        stepiv F_48c80 D_48c80 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepsd F_48c84 D_48c84 (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
          ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
        stepsd F_48c88 D_48c88 (Z_to_bv 64 (ff + 248)) (Z_to_bv 64 (fs + 4096 + 24576 + pos))
          ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact G2 | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N3 (Z_to_bv 64 (ff + 248)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 24576 + pos)))) with N4.
        stepiv F_48c8c D_48c8c (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepn F_48c90 D_48c90.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
    destruct (memtoshadow47_run r3 N4 rom (0x48c94 : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
    assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
    assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
    unhide Hshadow_dj. destruct Hshadow_dj as [SD1 SD2]. unhide Fs2. unhide R2.
    (* [comment removed for export] *)
    assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
                 rdn ASEGS N8 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk. assert (Hk' : (8 <= k <= 32)%Z) by lia.
      rewrite (rdn_ext ASEGS 8 N8 (F4c regs)); [| unorm; cbn; lia |].
      - unfold F4c. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
          repeat (rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ]);
          apply rdn_wbytes_hit8; unorm; lia.
      - intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
        unfold N8, N7, N6, N5, N4, N3, N2, N1.
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
      stepiv F_48c94 D_48c94 (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_48c98 D_48c98 (Z_to_bv 64 ff) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepn F_48c9c D_48c9c.                                                                              (* [comment removed for export] *)
      stepsd F_48ca0 D_48ca0 (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [exact GN4|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 32%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
      stepsd F_48ca4 D_48ca4 (Z_to_bv 64 (SB + ff / 8 + 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [unfold N5; do 1 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 32%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N6.
      stepsd F_48ca8 D_48ca8 (Z_to_bv 64 (SB + ff / 8 + 16)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [unfold N6, N5; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 32%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N7.
      stepsd F_48cac D_48cac (Z_to_bv 64 (SB + ff / 8 + 24)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ mem0); [unfold N7, N6, N5; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) _ 32%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N8.
      #[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; split; reflexivity].
      stepld F_48cb0 D_48cb0 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; slv).
      stepld F_48cb4 D_48cb4 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; slv).
      stepld F_48cb8 D_48cb8 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; slv).
      stepld F_48cbc D_48cbc (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; slv).
      stepiv F_48cc0 D_48cc0 (Z_to_bv 64 s) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepret F_48cc4 D_48cc4 ra ltac:(rwH; reflexivity).
      unfold N8, N7, N6, N5, N4, N3, N2, N1. fold (fsm2_mem M2).
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; symmetry; apply sp_sc|]. split; [gres; reflexivity|].
      split.
      + assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
        { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [apply keeps_but_cs; exact K2|].
          eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs; exact K4. }
        intros r Hcs. destruct (decide (r = 1%bv)) as [->|N1']; [gres; rewrite H1; reflexivity|].
        destruct (decide (r = 2%bv)) as [->|N2']; [gres; rewrite H2; reflexivity|].
        destruct (decide (r = 8%bv)) as [->|D8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|D9]; [gres; reflexivity|].
        destruct (decide (r = 18%bv)) as [->|D18]; [gres; reflexivity|].
        repeat (rewrite getr_other; [| intros ->; first [match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end | cbv in Hcs; clear -Hcs; intuition discriminate]]).
        apply KB; [exact Hcs|]. clear -N1' N2' D8 D9 D18. cbv. intuition congruence.
      + split; [exact O2' | exact G2].
  Qed.
End FSM2.
End FPX_1.
