(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the block lemma w6_kind of lib/A/RPgW6aBase.v,
   0x80ac8 .. the case entry of ent_build's `switch (kind % 10)` (pod.h:279-281, fuzz.h:37-43).
     0x80ac8  ld a0,0xf8(s1); beqz a0 -> 0x80bac          in.n = 0: stop at 0x80bac with a0 = 0
     0x80ad0 .. 0x80adc  the shadow check of s9 (NE-SLOW, slow block 0x81944 .. 0x8194c)
     0x80ae0  lbu a0,0(s9); s8 := s9; s9 := [R+0xf8] - 1
     0x80af0 .. 0x80b08  a1 := (b - 10 ((b * 0xcd) >> 11)) & 0xff = b mod 10; a7 := 10
     0x80b0c  a4 := s8; s8 += 1; a2 := 8; 0x80b18 bltu a2,a1 -> 0x81184 (case 9), else 0x80b1c
     0x80b1c .. 0x80b3c  RPgSteps.rl_jt_block, chained by w6_blk_seq.
   The engine's entry state: the s1-based region with the 8-byte chunk [R+0xf8] = |r| (atom 32), and when
   r = b :: r' the one-byte read-only region at the cursor s9 holding b (atom 33); the shadow base is s7 itself
   (SOff 23 0). The engine follows the check's slow block and leaves one obligation, paid from w6_in's
   range_addressable. Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSteps RPgW6aBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== kind % 10 ======================================== *)
(* the engine's a1 at 0x80b18, over the kind byte's atom 33 *)
Definition kd_a1 : sv :=
  SAlu ALU_AND
    (SAlu ALU_SUB (SOff 33 0)
       (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff 33 0) (SLit 205)) (SLit 11)) (SLit 10)))
    (SLit 255).
Definition kd_env (b : Z) : env := mkEnv (fun _ => Z_to_bv 64 b) (fun _ => []).
Lemma kd_all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true ->
  forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c).
split; [lia|]. apply in_seq. lia.
Qed.
Lemma kd_a1_env : forall E b, ew E 33 = Z_to_bv 64 b -> sv_denot E kd_a1 = sv_denot (kd_env b) kd_a1.
Proof. intros E b H. unfold kd_a1. cbn [sv_denot]. rewrite H. reflexivity. Qed.
Lemma kd_a1_mod : forall E b, ew E 33 = Z_to_bv 64 b -> 0 <= b < 256 -> sv_denot E kd_a1 = Z_to_bv 64 (b mod 10).
Proof.
intros E b H Hb. rewrite (kd_a1_env E b H). apply bv_eq. apply Z.eqb_eq.
exact (kd_all256 (fun b => bv_unsigned (sv_denot (kd_env b) kd_a1) =? bv_unsigned (Z_to_bv 64 (b mod 10)))
  ltac:(vm_compute; reflexivity) b Hb).
Qed.

(* ======================================== the entry states ======================================== *)
Definition kd_slot (v : sv) : YP09.region := YP09.mkRegion (Some 9%nat) 248 256 0 0 [YP09.mkChunk 248 (CVal 8 v)].
Definition kd_byte : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition kd_G : facts :=
  mkFacts [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF 1 (2 ^ 47 - 2) 0); (32%nat, mkAF 1 (2 ^ 63) 0);
           (33%nat, mkAF 0 255 0)] [] [].
Definition kd_ss1 : sstate := mkSS W6_RET sr_atoms [kd_slot (SOff 32 0); kd_byte] None kd_G.
Definition kd_ss0 : sstate := mkSS W6_RET sr_atoms [kd_slot (SLit 0)] None (mkFacts [] [] []).
Definition kd_Bx : sv := SOff 23 0.
Definition kd_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kd_extra (n b : Z) : list word := [w64 n; w64 b].
Definition kd_clob : list (bv 5) := [10; 11; 12; 14; 17; 24; 25]%bv.
(* the registers the run to 0x81184 / 0x80b1c sets: a0 = b, a1 = b mod 10, a2 = 8, a4 = the kind's address,
   s8 = the cursor after it, s9 = in.n - 1, a7 = 10 *)
Definition kd_Rc (b cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 10 = w64 b /\ getr regs2 11 = w64 (b mod 10) /\ getr regs2 12 = w64 8 /\ getr regs2 14 = w64 cur /\
getr regs2 24 = w64 (cur + 1) /\ getr regs2 25 = w64 nl' /\ getr regs2 17 = w64 10.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* a block post with fewer clobbered registers and a stronger R is a block post *)
Lemma rl_blk_post_mono : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob'
  (R R' : bvmap 5 word -> Prop) W2 c2,
  incl clob clob' ->
  (forall regs2, (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) -> R regs2 -> R' regs2) ->
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob R W2 c2 ->
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob' R' W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob clob' R R' W2 c2 Hi HR
  (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR2).
exists ly2, S2, regs2, mem2, md2. split; [exact Ec|]. split; [exact HJ|].
split; [intros r Hr0 Hn; apply Hr; [exact Hr0 | intros X; apply Hn; apply Hi; exact X]|].
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|]. split; [exact Hm|].
exact (HR regs2 Hr HR2).
Qed.

(* the frame's base R from the context: in [alloc_ceiling + T_SEG_STK, 2 ^ 47) *)
Lemma kd_R_range : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  alloc_ceiling + T_SEG_STK <= R /\ R + 0x1a0 <= 2 ^ 47.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & _ & H1 & H2 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (A1 & A2 & A3 & A4 & A5 & A6 & _) & _).
lia.
Qed.

(* ---- the case r = [] ---- *)
Lemma kd_nil : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos,
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 9 = w64 R -> val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 0 ->
  SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
  (rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_D0E [10]%bv
    (fun regs2 => getr regs2 10 = w64 0)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H9 Hn.
pose proof (kd_R_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as HRr.
pose proof Hctx as (HJ & _).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof alloc_ceiling_value as Hceil. unfold T_SEG_STK, ASTACK in HRr.
assert (E9 : ew (Ereg regs []) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (HS : st_ok rsegs (Ereg regs []) kd_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, kd_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ R 248 8 (SLit 0) 0); [reflexivity | lia | lia | exact Hn].
  - cbn. tauto.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 W6_RET) with (Z_to_bv 64 W6_RET).
aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_D0E;
[ awr_ok_tac | ].
apply SRr_ret. red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply RPgCfgChanges.same_io_wvb|].
split; [apply mo_le_refl; assumption|].
split.
- intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]]; cbn in Hr; lia.
- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
  lazymatch type of HS with st_ok _ _ ?ssf _ =>
    let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
    change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 end.
  reflexivity.
Qed.

(* ---- the case r = b :: r': the run to 0x80b18, the branch on b mod 10, the run to its target ---- *)
Ltac kd_finish ms2 HS HJ HAE2 HFr1 HFr lyc Sc regs W :=
  apply SRr_ret;
  lazymatch goal with |- _ (mkCfg ms2 ?md2) => red; exists lyc, Sc, (ms_regs ms2), (ms_mem ms2), md2 end;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms2 HS eq_refl) at 1; reflexivity|];
  split; [exact HJ|];
  split; [eapply (regs_kept_of_st_ok rsegs _ _ ms2 regs _ (w_H W) _ HS HAE2); vm_compute; reflexivity|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ let a := fresh "a" in
    intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [rewrite (HFr1 (Z_to_bv 64 a)); [reflexivity|]|];
    let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros (rr & Hin & Hr); cbv [In ss_mem add_cond kd_ss1] in Hin; destruct Hin as [<-|[<-|[]]]; cbn in Hr; lia
  | unfold kd_Rc; rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms2 _ HS);
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
      let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
      let e14 := eval vm_compute in (sr_get (ss_regs ssf) (14%bv : bv 5)) in
      let e17 := eval vm_compute in (sr_get (ss_regs ssf) (17%bv : bv 5)) in
      let e24 := eval vm_compute in (sr_get (ss_regs ssf) (24%bv : bv 5)) in
      let e25 := eval vm_compute in (sr_get (ss_regs ssf) (25%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
      change (sr_get (ss_regs ssf) (11%bv : bv 5)) with kd_a1;
      change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
      change (sr_get (ss_regs ssf) (14%bv : bv 5)) with e14;
      change (sr_get (ss_regs ssf) (17%bv : bv 5)) with e17;
      change (sr_get (ss_regs ssf) (24%bv : bv 5)) with e24;
      change (sr_get (ss_regs ssf) (25%bv : bv 5)) with e25 end ].

Lemma kd_cons : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos cur
  (bb : byte) (r' : list byte),
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  getr regs 9 = w64 R -> getr regs 23 = w64 SHADOW_OFF -> getr regs 25 = w64 cur ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (Z.of_nat (length (bb :: r'))) ->
  w6_in W memc R cur (bb :: r') ->
  SRr rsegs W (cfg_at rsegs W6_RET regs memc mdc)
  (rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
    (if bv_unsigned bb mod 10 =? 9 then W6_D9 else W6_JT) kd_clob
    (kd_Rc (bv_unsigned bb) cur (Z.of_nat (length r')))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r' Hctx H9 H23 H25 Hn Hin.
pose proof (kd_R_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx) as HRr.
pose proof Hctx as (HJ & _).
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof alloc_ceiling_value as Hceil. unfold T_SEG_STK, ASTACK in HRr.
pose proof (Cursor.byte_range bb) as Hb.
destruct Hin as (Hg & Hra & Hc0 & Hc1 & Hamem & Hdis).
remember (Z.of_nat (length (bb :: r'))) as n eqn:Hneq.
assert (Hn1 : n = 1 + Z.of_nat (length r')) by (rewrite Hneq; cbn [length]; lia).
pose proof (Hdis cur ltac:(lia)) as Hdc. clear Hdis. unfold T_SEG_STK, ASTACK in Hdc.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamem.
destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv0 _]. clear Hg.
cbn [nth map Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
remember (bv_unsigned bb) as b eqn:Hbeq.
pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
assert (E9 : ew (Ereg regs (kd_extra n b)) 9 = Z_to_bv 64 R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E23 : ew (Ereg regs (kd_extra n b)) 23 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (E25 : ew (Ereg regs (kd_extra n b)) 25 = Z_to_bv 64 cur)
  by (rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew (Ereg regs (kd_extra n b)) 32 = Z_to_bv 64 n) by exact (ew_Ereg_extra regs (kd_extra n b) 0).
assert (E33 : ew (Ereg regs (kd_extra n b)) 33 = Z_to_bv 64 b) by exact (ew_Ereg_extra regs (kd_extra n b) 1).
assert (HS : st_ok rsegs (Ereg regs (kd_extra n b)) kd_ss1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 W6_RET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, kd_slot. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ R 248 8 (SOff 32 0) n);
        [cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Hn].
    + unfold region_ok, kd_byte. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E25, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 33 0) b);
        [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 1)) with 256; lia | lia | rewrite Z.add_0_r; exact Hv0].
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, kd_slot, kd_byte.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E25, !unsigned_lit_small by lia.
    repeat split; first [exact I | lia].
  - assert (HF23 : afact_ok (Ereg regs (kd_extra n b)) 23 (mkAF SHADOW_OFF SHADOW_OFF 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E23, unsigned_lit_small by (unfold SHADOW_OFF; lia).
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF25 : afact_ok (Ereg regs (kd_extra n b)) 25 (mkAF 1 (2 ^ 47 - 2) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF32 : afact_ok (Ereg regs (kd_extra n b)) 32 (mkAF 1 (2 ^ 63) 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    assert (HF33 : afact_ok (Ereg regs (kd_extra n b)) 33 (mkAF 0 255 0)).
    { unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
      split; [lia|]. split; [apply Z.mod_1_r | lia]. }
    exact (conj (conj HF23 (conj HF25 (conj HF32 (conj HF33 I)))) (conj I I)). }
assert (SHOK : sh_ok rsegs kd_Bx [] (Ereg regs (kd_extra n b)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 34 (Ereg regs (kd_extra n b)) (Ereg regs (kd_extra n b))) by apply env_agree_refl.
unfold cfg_at. change (w64 W6_RET) with (Z_to_bv 64 W6_RET).
aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_JT.
{ eapply obl_of_range; [exact Hra | | |].
  - unfold kd_Bx. apply (U_atom _ 23 SHADOW_OFF E23). unfold SHADOW_OFF. lia.
  - rewrite (U_atom _ 25 cur E25) by lia. lia.
  - rewrite (U_atom _ 25 cur E25) by lia. lia. }
{ awr_ok_tac. }
rename HFr into HFr1.
lazymatch type of HS with st_ok _ ?E1 _ _ =>
  assert (HAE1 : env_agree 34 (Ereg regs (kd_extra n b)) E1) by env_agree_chain HAE end.
pose proof HAE1 as [HA1 _].
assert (E33' : forall E', (forall i, (i < 34)%nat -> ew E' i = ew (Ereg regs (kd_extra n b)) i) ->
  ew E' 33 = Z_to_bv 64 b) by (intros E' HE'; rewrite (HE' 33%nat) by lia; exact E33).
srr_branch_tok w6_tbl_ok HS SHOK kd_span.
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E33' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_lt in Hc.
  assert (Hm9 : b mod 10 = 9) by lia. rewrite (proj2 (Z.eqb_eq _ _) Hm9).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_D9.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 34 (Ereg regs (kd_extra n b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra n b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [cbn [sv_denot]; rewrite (HA2 33%nat) by lia; rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [exact (kd_a1_mod _ b (E33' _ HA2) ltac:(lia))|].
  split; [reflexivity|].
  cbn [sv_denot]. rewrite (HA2 25%nat), (HA2 32%nat) by lia. rewrite E25, E32, !unsigned_lit_small by lia.
  unfold w64. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia | reflexivity].
- fold kd_a1 in Hc. rewrite branch_ltu_U in Hc. unfold U in Hc.
  rewrite (kd_a1_mod _ b (E33' _ HA1) ltac:(lia)) in Hc. cbn [sv_denot] in Hc.
  rewrite !unsigned_lit_small in Hc by lia.
  apply Z.ltb_ge in Hc.
  assert (Hm9 : b mod 10 <> 9) by lia. rewrite (proj2 (Z.eqb_neq _ _) Hm9).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK kd_span W6_JT.
  { awr_ok_tac. }
  lazymatch type of HS with st_ok _ ?E2 _ (restrict _ ?ms2) =>
    assert (HAE2 : env_agree 34 (Ereg regs (kd_extra n b)) E2) by env_agree_chain HAE;
    assert (HAE2' : env_agree 32 (Ereg regs (kd_extra n b)) E2) by (eapply env_agree_le; [|exact HAE2]; lia);
    pose proof HAE2 as [HA2 _];
    kd_finish ms2 HS HJ HAE2' HFr1 HFr lyc Sc regs W end.
  split; [cbn [sv_denot]; rewrite (HA2 33%nat) by lia; rewrite E33, unsigned_lit_small by lia; unfold w64; f_equal; lia|].
  split; [exact (kd_a1_mod _ b (E33' _ HA2) ltac:(lia))|].
  split; [reflexivity|].
  cbn [sv_denot]. rewrite (HA2 25%nat), (HA2 32%nat) by lia. rewrite E25, E32, !unsigned_lit_small by lia.
  unfold w64. split; [f_equal; lia|]. split; [f_equal; lia|]. split; [f_equal; lia | reflexivity].
Qed.

(* ======================================== the theorem ======================================== *)
Theorem w6_kind : w6_kind_stmt B MT.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur r Hctx H9 H23 H25 Hn Hin.
destruct r as [|bb r'].
- eapply SRr_mono; [exact (kd_nil STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos Hctx H9 Hn)|].
  intros W2 c2 _ HP. left. split; [reflexivity | exact HP].
- assert (Hrom : rom_view rsegs W memc) by (destruct Hctx as (_ & _ & _ & _ & _ & _ & X); exact X).
  pose proof (kd_cons STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur bb r'
    Hctx H9 H23 H25 Hn Hin) as H1.
  pose proof (Cursor.byte_range bb) as Hb.
  remember (bv_unsigned bb) as b eqn:Hbeq.
  remember (Z.of_nat (length r')) as nl eqn:Hnl.
  pose proof (Z.mod_pos_bound b 10 ltac:(lia)) as Hm.
  eapply SRr_mono; [| intros W2 c2 _ HP; right; exists bb, r'; split; [reflexivity | rewrite <- Hbeq, <- Hnl; exact HP]].
  unfold w6_case_pc, w6_kind_clob.
  destruct (Z.eqb_spec (b mod 10) 9) as [E9|E9].
  + eapply SRr_mono; [exact H1|]. intros W2 c2 _ HP.
    apply rl_blk_post_mono with (clob := kd_clob) (R := kd_Rc b cur nl); [apply incl_refl | | exact HP].
    intros regs2 _ (R10 & R11 & R12 & R14 & R24 & R25 & R17).
    unfold w6_kind_R. rewrite (proj2 (Z.eqb_eq _ _) E9). rewrite E9 in R11.
    repeat split; assumption.
  + eapply SRr_mono.
    * eapply (w6_blk_seq B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6_RET W6_JT
        (jt_tgt (b mod 10)) kd_clob [10; 11; 12; 20]%bv (kd_Rc b cur nl) (w6_kind_R b cur nl)).
      { exact H1. }
      intros W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 (R10 & R11 & R12 & R14 & R24 & R25 & R17).
      assert (Hrom1 : rom_view rsegs W1 mem1) by (intros a Ha; rewrite Hm1; exact (Hrom a Ha)).
      eapply SRr_mono;
        [exact (rl_jt_block B MT MTL LAWS STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k regs1 (b mod 10)
                  HJ1 ltac:(lia) R11 Hrom1)|].
      intros W2 c2 _ HP.
      apply rl_blk_post_mono with (clob := [10; 11; 12; 20]%bv) (R := jt_R (b mod 10) regs1);
        [apply incl_refl | | exact HP].
      intros regs2 Hk (J11 & J12 & J10 & J20).
      rewrite R10 in J10, J20. unfold w64 in J10, J20. rewrite unsigned_lit_small in J10, J20 by lia.
      rewrite (Z.mod_small b 256) in J20 by lia.
      unfold w6_kind_R. rewrite (proj2 (Z.eqb_neq _ _) E9).
      rewrite !Hk by (cbv; first [discriminate | intros [X|[X|[X|[X|[]]]]]; discriminate X]).
      repeat split; assumption.
    * intros W2 c2 _ HP. cbv beta iota.
      apply rl_blk_post_mono with (clob := kd_clob ++ [10; 11; 12; 20]%bv) (R := w6_kind_R b cur nl);
        [| intros regs2 _ X; exact X | exact HP].
      intros x Hx. apply in_app_or in Hx. cbn [kd_clob In] in Hx |- *. tauto.
Qed.

End d.
End b.

Print Assumptions w6_kind.
