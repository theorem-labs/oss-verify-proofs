(* Modified by Theorem Labs, 2026-10: the entry states, the engine runs and the 256-value check follow
   proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 (w6_c2h, c2_idx_block,
   c2_ld_block) for reac-pw/fuzz_rate's image A: rate's pcs, registers (the cursor in s9, the shadow offset in s2) and
   cells; the index is i % 9 and the load is the checked 8-byte load of vocab[i]; the lemmas end at the strlen
   wrapper's entry in continuation form. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the head of ent_build's
   case 1 (pod.h:286-287) inside LLVMFuzzerTestOneInput, from the case entry 0x817c4 to the strlen wrapper's entry
   0x42194. Proves no function (kind: segment lemma).
   THE CODE (registers as lib/A/RtPgW6bBase.v w6b_in: s1 = R, s2 = SHADOW_OFF, s9 = c, a4 = c - 1, s8 = |r|,
   a5 = |r| + 1):
     0x817c4  beqz s8 -> 0x81a2c                     no byte left: i = 0
     0x817c8 .. 0x817d4  the shadow check of s9 (NE-SLOW, slow block 0x821a0)
     0x817d8  lbu a0,0(s9); s10 := a5 - 2; a4 := a4 + 2; 0x817e4 .. 0x817fc a0 := i % 9 (mul 0x39, srli 9); j 0x81a38
     0x81a2c  s10 := 0; a0 := 0; a4 := s9
     0x81a38  sd a4,0x100(s1); a0 := 0x9bac0 + 8 a0 (&vocab[a0])          (c1_head, both arms, to 0x81a4c)
     0x81a4c .. 0x81a58  the shadow check of the 8-byte load (lbu; beqz; else `j` to the error path)
     0x81a60  ld s11,0(a0); mv a0,s11; 0x81a68 jal 0x42194 (ra = 0x81a6c)    (c1_vload)
   HOW. c1_vload: a0 is the register atom x10 (so the engine sees the check's `(x >> 3) + s2` form), the 8-byte cell
   a one-chunk region based at it whose value is the extra env slot 32 (w6b_vocab_ok gives the cell); the check
   leaves the obligation range_addressable (&vocab[i]) 8, a sub-range of vocab's 72 registered bytes. c1_head: the
   spill cell [R+0x100, R+0x108) a written region based at s1 (the callers' stack window), the input byte a
   one-byte region based at s9 whose value is slot 32; the check of s9 leaves range_addressable c 1 (w6_in); the
   no-byte arm pins s8 to 0; a0 at 0x81a4c is checked for all 256 values of the byte (c1h_a0_val). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW6aBase RtPgW6bBase RtPgW6bC1Kit.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RtPgSteps.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== the entry states ======================================== *)
(* the spill cell [R+0x100, R+0x108), written *)
Definition c1h_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x100 0x108 0x100 0x108 [].
(* the index byte at c (slot 32) *)
Definition c1h_rI : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition c1h_facts1 : facts :=
  mkFacts [c1_fR; c1_shf; (24%nat, mkAF 1 (2 ^ 47) 0); (25%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition c1h_ss1 : sstate := mkSS W6B_D1 sr_atoms [c1h_rR; c1h_rI] None c1h_facts1.
Definition c1h_ss0 : sstate := mkSS W6B_D1 sr_atoms [c1h_rR] None (mkFacts [c1_fR; c1_shf] [] []).
(* the vocab cell at a0 (slot 32 = vocab[i]) *)
Definition c1v_rV : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition c1v_ss : sstate := mkSS C1_V sr_atoms [c1v_rV] None
  (mkFacts [c1_shf; (10%nat, mkAF W6B_VOCAB (W6B_VOCAB + 64) 3)] [] []).
(* the registers each block may change *)
Definition c1v_clob : list (bv 5) := [1; 10; 11; 27]%bv.
Definition c1_hclob : list (bv 5) := [1; 10; 11; 12; 14; 24; 26; 27]%bv.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x81a4c as the engine computes it from the byte (slot 32) *)
Definition c1h_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9).
Definition c1h_a0 : sv :=
  SAlu ALU_ADD (SLit 637632)
    (SAlu ALU_SLL
       (SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 32 0) c1h_q) (SAlu ALU_SLL c1h_q (SLit 3))) (SLit 255))
       (SLit 3)).
Definition c1_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c1h_a0_val : forall E m, ew E 32 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c1h_a0 = Z_to_bv 64 (W6B_VOCAB + 8 * (m mod 9)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c1_envz m) c1h_a0); [unfold c1h_a0, c1h_q; cbn [sv_denot ew c1_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c1_all256 (fun m => bv_unsigned (sv_denot (c1_envz m) c1h_a0) =? bv_unsigned (Z_to_bv 64 (W6B_VOCAB + 8 * (m mod 9))))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* ---- 0x81a4c .. the strlen wrapper's entry: the checked load of vocab[j] ---- *)
Lemma c1_vload : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) j
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 (W6B_VOCAB + 8 * j) -> 0 <= j < 9 -> getr regs 18 = w64 SHADOW_OFF ->
  w6b_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1v_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1_RSTR -> getr regs1 10 = w64 (w6b_vptr j) -> getr regs1 27 = w64 (w6b_vptr j) ->
    (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6B_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1_V regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs j Q HJ H10 Hj H18 (Hra & Hv) K.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs. pose proof LAWS as HL.
destruct (Hv j Hj) as [Hcell Hcs].
pose proof (c1_vptr_range j Hj) as Hvp.
set (E := Ereg regs [w64 (w6b_vptr j)]).
assert (E10 : ew E 10 = Z_to_bv 64 (W6B_VOCAB + 8 * j)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 (w6b_vptr j)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok rsegs E c1v_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_V) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, c1v_rV.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by (unfold W6B_VOCAB; lia).
    split; [unfold W6B_VOCAB; lia|]. split; [unfold W6B_VOCAB; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0 8 (SOff 32 0) (w6b_vptr j)).
    + apply rts_den_atom; [exact E32 | lia].
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact Hcell.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1v_ss ss_facts c1_shf].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c1_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c1_af _ _ _ _ _ _ E10); unfold W6B_VOCAB; [lia | lia | | lia].
      change (2 ^ 3) with 8. rewrite (Z.mul_comm 8 j). rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs C1_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [w64 (w6b_vptr j)]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
clearbody E.
unfold cfg_at. change (w64 C1_V) with (Z_to_bv 64 C1_V).
aj_run_to_tok w6_tbl_ok HS HJ SHOK C1_span W6B_STRLEN.
- apply (obl_of_range rsegs (w_H W) memc _ C1_Bx _ _ W6B_VOCAB 72 Hra).
  + apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 10 (W6B_VOCAB + 8 * j) E10) by (unfold W6B_VOCAB; lia). lia.
  + rewrite (U_atom _ 10 (W6B_VOCAB + 8 * j) E10) by (unfold W6B_VOCAB; lia). lia.
- awr_ok_tac.
- c1_keep.
  lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
    replace (ss_pc ss) with W6B_STRLEN by (vm_compute; reflexivity) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 W6B_STRLEN) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6B_STRLEN rg mm md) end.
  apply K.
  + exact HJ.
  + c1_kio.
  + apply (regs_kept_of_st_ok rsegs _ _ _ regs [w64 (w6b_vptr j)] (w_H W) c1v_clob HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + c1_regv HS (1%bv : bv 5). reflexivity.
  + c1_regv HS (10%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + c1_regv HS (27%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + exact KE.
Qed.

(* ---- 0x817c4 .. the strlen wrapper's entry ---- *)
Lemma c1_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c vb pp kd : Z)
  (r : list byte) (Q : world rsegs -> config -> Prop),
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6b_in B W memc regs R F c vb pp kd r ->
  w6b_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1_hclob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1_RSTR -> getr regs1 10 = w64 (w6b_vptr (c1_j r)) -> getr regs1 27 = w64 (w6b_vptr (c1_j r)) ->
    getr regs1 26 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x100 <= a < R + 0x108) -> aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x100) 8 (c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))) ->
    SRr rsegs W (cfg_at rsegs W6B_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs W6B_D1 regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp kd r Q Hctx Hin Hvoc K.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H18 & H25 & H14 & H24 & H15 & H23 & H27 & H26 & H22 & V60 & Vb0 & Vc0 & Ve8 &
  V108 & V118 & V138 & Hvb & Hkd & Hpp & Hpp2 & HF4 & HF5 & HF32 & HFapp & Hez & Hera & Hehu & Hc1 & Hw6in & Hrhu & Hrdis).
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs. pose proof LAWS as HL.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HRb : 0x7fff7f800000 <= R /\ R + 0x1e0 <= 2 ^ 47) by lia.
destruct Hw6in as (Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
assert (U9 : forall extra, bv_unsigned (ew (Ereg regs extra) 9) = R).
{ intros extra. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (Hc0vl : forall o, 0x100 <= o < 0x108 -> writable_at rsegs (mrestrict (w_H W) memc) (R + o)).
{ intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia. }
destruct r as [|b r'].
- (* no byte left: i = 0 *)
  set (E := Ereg regs []).
  assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E25 : ew E 25 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (HS0 : st_ok rsegs E c1h_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor]. unfold region_ok, c1h_rR.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. subst E. rewrite U9.
      split; [lia|]. split; [lia|]. split; [exact Hc0vl | constructor].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1h_ss0 ss_facts c1_shf c1_fR].
      split; [|split; exact I]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. subst E. rewrite U9. change (2 ^ 4) with 16. lia.
      + apply (c1_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (24%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H24; reflexivity)) as HS.
  clear HS0.
  assert (SHOK : sh_ok rsegs C1_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  clearbody E.
  unfold cfg_at. change (w64 W6B_D1) with (Z_to_bv 64 W6B_D1).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK C1_span C1_V.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  (* the bytes outside the spill cell are kept; the spill cell holds c *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x100 <= a < R + 0x108) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1h_ss0 In] in Hin; destruct Hin as [<-|[]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1h_rR] in Hr; rewrite UE9 in Hr; lia |];
  assert (VS : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x100) 8 c);
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rts_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rts_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x100 (CVal 8 (SOff 25 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x100 8 (SOff 25 0) c Hc
        ltac:(apply rts_den_atom; [rewrite ?ew_ewset_other by lia; exact E25 | lia]) ltac:(lia) ltac:(cbn; lia))
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) [10; 11; 12; 14; 24; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 0) by (c1_regv HS (26%bv : bv 5); reflexivity);
  apply (c1_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) 0 Q HJ)
  end.
  + c1_regv HS (10%bv : bv 5). reflexivity.
  + lia.
  + rewrite RK by c1_out. exact H18.
  + apply (c1_vocab_lowk W memc); [|exact Hvoc].
    apply (c1_lowk_of W memc _ (fun a => R + 0x100 <= a < R + 0x108) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G27 Hm1.
    apply K; cbn [fuzz_u8 fst snd length Z.of_nat].
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1_kio.
    * intros rg Hr0 Hn. rewrite (Hk1 rg Hr0 (c1_incl_sub c1v_clob c1_hclob rg ltac:(intros x Hx; cbn [In c1v_clob c1_hclob] in *; tauto) Hn)).
      apply RK; [exact Hr0|]. intros X. apply Hn. cbn [In c1_hclob] in *. tauto.
    * exact G1.
    * exact G10.
    * exact G27.
    * rewrite Hk1 by c1_out. exact R26.
    * intros a Ha Hn. rewrite Hm1. exact (KR a Ha Hn).
    * apply (rts_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x100) 8); [intros q Hq; apply Hm1|].
      match goal with |- val_mem _ _ _ _ ?v => replace v with c by (cbn; lia) end. exact VS.
- (* a byte m = b, the rest r' *)
  cbn [fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : ~ (R + 0x60 <= c < R + 0x120)) by (destruct (Hdis c ltac:(lia)) as (_ & Hd & _); exact Hd).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  set (E := Ereg regs [w64 m]).
  assert (E14 : ew E 14 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
  assert (E15 : ew E 15 = Z_to_bv 64 (n + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
  assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E24 : ew E 24 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact H24).
  assert (E25 : ew E 25 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
  assert (E32 : ew E 32 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  assert (HS : st_ok rsegs E c1h_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c1h_rR.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. subst E. rewrite U9.
        split; [lia|]. split; [lia|]. split; [exact Hc0vl | constructor].
      + unfold region_ok, c1h_rI.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E25, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 32 0) m);
          [apply rts_den_atom; [exact E32 | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1h_rR, c1h_rI.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UE9, E25, !unsigned_lit_small by lia.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1h_ss1 ss_facts c1h_facts1 c1_shf c1_fR].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UE9. change (2 ^ 4) with 16. lia.
      + apply (c1_af _ _ _ _ _ _ E18); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c1_af _ _ _ _ _ _ E24); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1_af _ _ _ _ _ _ E25); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1_af _ _ _ _ _ _ E32); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  assert (SHOK : sh_ok rsegs C1_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs [w64 m]) E) by (subst E; apply env_agree_refl).
  clearbody E.
  unfold cfg_at. change (w64 W6B_D1) with (Z_to_bv 64 W6B_D1).
  aj_run_to_tok w6_tbl_ok HS HJ SHOK C1_span C1_V.
  { apply (obl_of_range rsegs (w_H W) memc _ C1_Bx _ _ c n Hrain).
    - apply (U_atom _ 18 SHADOW_OFF E18). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia.
    - rewrite (U_atom _ 25 c E25) by lia. lia. }
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x100 <= a < R + 0x108) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn'; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1h_ss1 In] in Hin; destruct Hin as [<-|[<-|[]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1h_rR c1h_rI] in Hr; rewrite ?UE9, ?E25 in Hr;
    [lia | lia] |];
  assert (VS : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x100) 8 (c + 1));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rts_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rts_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x100 (CVal 8 (SOff 14 2))) ltac:(cbn; tauto)) as Hc;
      refine (val_of_chunk_ok rsegs Ef _ R 0x100 8 (SOff 14 2) (c + 1) Hc _ ltac:(lia) ltac:(cbn; lia));
      apply bv_eq; rewrite denot_SOff; rewrite ?ew_ewset_other by lia; rewrite E14;
      rewrite !unsigned_lit_small by lia; rewrite zcanon_id by (unfold M64; lia); lia
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [w64 m] (w_H W) [10; 11; 12; 14; 26]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 (Z.of_nat (length r')));
  [ c1_regv HS (26%bv : bv 5); rewrite E15, unsigned_lit_small by lia; unfold w64; f_equal; lia |];
  assert (R10 : getr (ms_regs ms) 10 = w64 (W6B_VOCAB + 8 * (m mod 9)));
  [ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS);
    replace (sr_get (ss_regs ss) (10%bv : bv 5)) with c1h_a0 by (vm_compute; reflexivity);
    apply c1h_a0_val; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hmb] |];
  apply (c1_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) (m mod 9) Q HJ R10)
  end.
  + apply Z.mod_pos_bound. lia.
  + rewrite RK by c1_out. exact H18.
  + apply (c1_vocab_lowk W memc); [|exact Hvoc].
    apply (c1_lowk_of W memc _ (fun a => R + 0x100 <= a < R + 0x108) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G27 Hm1.
    apply K.
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1_kio.
    * intros rg Hr0 Hn'. rewrite (Hk1 rg Hr0 (c1_incl_sub c1v_clob c1_hclob rg ltac:(intros x Hx; cbn [In c1v_clob c1_hclob] in *; tauto) Hn')).
      apply RK; [exact Hr0|]. intros X. apply Hn'. cbn [In c1_hclob] in *. tauto.
    * exact G1.
    * unfold c1_j. cbn [fuzz_u8 fst]. exact G10.
    * unfold c1_j. cbn [fuzz_u8 fst]. exact G27.
    * cbn [fuzz_u8 snd]. rewrite Hk1 by c1_out. exact R26.
    * intros a Ha Hn'. rewrite Hm1. exact (KR a Ha Hn').
    * cbn [fuzz_u8 snd]. apply (rts_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x100) 8); [intros q Hq; apply Hm1|].
      replace (c + n - Z.of_nat (length r')) with (c + 1) by lia. exact VS.
Qed.
End d.
End b.

Print Assumptions c1_vload.
Print Assumptions c1_head.
