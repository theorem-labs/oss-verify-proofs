(* Modified by Theorem Labs, 2026-10: the entry states, the engine runs and the 256-value check follow
   proofs/reac-pw/fuzz_role/lib/A/RPgW6aC2h.v at 616508a91de2 (w6_c2h, c2_idx_block,
   c2_ld_block) for reac-pw/fuzz_rate's image A: rate's pcs, registers (the cursor in s9, the shadow offset in s2) and
   cells; the index is i % 9 and the load is the checked 8-byte load of vocab[i]; the lemmas end at the strlen
   wrapper's entry in continuation form. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC1Head.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the pcs, the registers (the cursor in s2, the shadow offset in s4, what is left in s6 and
   t1, the string in s9) and the vocab table's address are image B's; the head writes the two spill cells [R+0x70]
   (what is left) and [R+0x128] (the kind byte) instead of [R+0x100]; the UBSan tests T1 0x81908 and T2 0x81950 are
   decided by the engine (a6 pinned to 1, the cursor's and the index's closed ranges); the prefix c1_ becomes c1b_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the head of ent_build's
   case 1 (pod.h:286-287) inside LLVMFuzzerTestOneInput, from the case entry 0x81900 to the strlen wrapper's entry
   0x421ec. Proves no function (kind: segment lemma).
   THE CODE (registers as lib/AU/RtPgW6bBaseB.v w6bb_in: s1 = R, s4 = SHADOW_OFF, s2 = c, s10 = c - 1, s6 = |r|,
   t1 = |r| + 1, a6 = 1, a3 = the kind byte sign-extended):
     0x81900  beqz s6 -> 0x81b74                     no byte left: i = 0
     0x81904  a0 := s2 + 1; 0x81908 bltu a6,a0 (T1; else the `unimp`)
     0x81910 .. 0x8191c  the shadow check of s2 (NE-SLOW, slow block 0x822c8)
     0x81920  lbu a1,0(s2); a0 := 0x9bdc0; 0x8192c .. 0x81948 a1 := 8 (i % 9) (mul 0x39, srli 9, subw, zext.b)
     0x8194c  a2 := ~a0; 0x81950 bgeu a2,a1 (T2; else the `unimp`); t1 := t1 - 2; s10 := s10 + 2; a0 := a0 + a1;
              j 0x81b84
     0x81b74  t1 := 0; a0 := 0x9bdc0; s10 := s2
     0x81b84  sd a3,0x128(s1); sd t1,0x70(s1)                  (c1b_head, both arms, to 0x81b8c)
     0x81b8c .. 0x81b9c  the shadow check of the 8-byte load (lbu; beqz; else `j` to the error path)
     0x81ba0  ld s9,0(a0); mv a0,s9; 0x81ba8 jal 0x421ec (ra = 0x81bac)    (c1b_vload)
   HOW. c1b_vload: a0 is the register atom x10 (so the engine sees the check's `(x >> 3) + s4` form), the 8-byte cell
   a one-chunk region based at it whose value is the extra env slot 32 (w6bb_vocab_ok gives the cell); the check
   leaves the obligation range_addressable (&vocab[i]) 8, a sub-range of vocab's 72 registered bytes. c1b_head: the
   spill cells [R+0x70, R+0x78) and [R+0x128, R+0x130) two written regions based at s1 (the callers' stack window),
   the input byte a one-byte region based at s2 whose value is slot 32; a6 is pinned to 1 and the cursor (atom 18)
   carries [1, 2^47 - 1], which decides T1; the index's range [0, 2040] decides T2; the check of s2 leaves
   range_addressable c 1 (w6bb_inp); the no-byte arm pins s6 to 0; a0 at 0x81b8c is checked for all 256 values of the
   byte (c1bh_a0_val). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgMemB RtPgStepsB RtPgW6bBaseB RtPgW6bC1KitB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RtPgStepsB.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the entry states ======================================== *)
(* the spill cells [R+0x70, R+0x78) and [R+0x128, R+0x130), written *)
Definition c1bh_r70 : YP09.region := YP09.mkRegion (Some 9%nat) 0x70 0x78 0x70 0x78 [].
Definition c1bh_r128 : YP09.region := YP09.mkRegion (Some 9%nat) 0x128 0x130 0x128 0x130 [].
(* the index byte at c (slot 32) *)
Definition c1bh_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition c1bh_facts1 : facts :=
  mkFacts [c1b_fR; c1b_shf; (22%nat, mkAF 1 (2 ^ 47) 0); (18%nat, mkAF 1 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition c1bh_ss1 : sstate := mkSS W6BB_D1 sr_atoms [c1bh_r70; c1bh_r128; c1bh_rI] None c1bh_facts1.
Definition c1bh_ss0 : sstate := mkSS W6BB_D1 sr_atoms [c1bh_r70; c1bh_r128] None (mkFacts [c1b_fR; c1b_shf] [] []).
(* the vocab cell at a0 (slot 32 = vocab[i]) *)
Definition c1bv_rV : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition c1bv_ss : sstate := mkSS C1B_V sr_atoms [c1bv_rV] None
  (mkFacts [c1b_shf; (10%nat, mkAF W6BB_VOCAB (W6BB_VOCAB + 64) 3)] [] []).
(* the registers each block may change (the head's run: t1, a0, a1, a2, s10, and a6 and s6 pinned) *)
Definition c1bv_clob : list (bv 5) := [1; 10; 11; 25]%bv.
Definition c1bh_rclob : list (bv 5) := [6; 10; 11; 12; 16; 22; 26]%bv.
Definition c1b_hclob : list (bv 5) := [1; 6; 10; 11; 12; 16; 22; 25; 26]%bv.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x81b8c as the engine computes it from the byte (slot 32) *)
Definition c1bh_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 32 0) (SLit 57)) (SLit 9).
Definition c1bh_a0 : sv :=
  SAlu ALU_ADD (SLit 638400)
    (SAlu ALU_SLL
       (SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 32 0) c1bh_q) (SAlu ALU_SLL c1bh_q (SLit 3))) (SLit 255))
       (SLit 3)).
Definition c1b_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c1bh_a0_val : forall E m, ew E 32 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c1bh_a0 = Z_to_bv 64 (W6BB_VOCAB + 8 * (m mod 9)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c1b_envz m) c1bh_a0); [unfold c1bh_a0, c1bh_q; cbn [sv_denot ew c1b_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c1b_all256 (fun m => bv_unsigned (sv_denot (c1b_envz m) c1bh_a0) =? bv_unsigned (Z_to_bv 64 (W6BB_VOCAB + 8 * (m mod 9))))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* ---- 0x81b8c .. the strlen wrapper's entry: the checked load of vocab[j] ---- *)
Lemma c1b_vload : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) j
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 (W6BB_VOCAB + 8 * j) -> 0 <= j < 9 -> getr regs 20 = w64 SHADOW_OFF ->
  w6bb_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1bv_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1B_RSTR -> getr regs1 10 = w64 (w6bb_vptr j) -> getr regs1 25 = w64 (w6bb_vptr j) ->
    (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6BB_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1B_V regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs j Q HJ H10 Hj H20 (Hra & Hv) K.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs. pose proof LAWS as HL.
destruct (Hv j Hj) as [Hcell Hcs].
pose proof (c1b_vptr_range j Hj) as Hvp.
set (E := Ereg regs [w64 (w6bb_vptr j)]).
assert (E10 : ew E 10 = Z_to_bv 64 (W6BB_VOCAB + 8 * j)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 (w6bb_vptr j)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok rsegs E c1bv_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1B_V) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, c1bv_rV.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10, unsigned_lit_small by (unfold W6BB_VOCAB; lia).
    split; [unfold W6BB_VOCAB; lia|]. split; [unfold W6BB_VOCAB; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0 8 (SOff 32 0) (w6bb_vptr j)).
    + apply rtsb_den_atom; [exact E32 | lia].
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact Hcell.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bv_ss ss_facts c1b_shf].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c1b_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c1b_af _ _ _ _ _ _ E10); unfold W6BB_VOCAB; [lia | lia | | lia].
      change (2 ^ 3) with 8. rewrite (Z.mul_comm 8 j). rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [w64 (w6bb_vptr j)]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
clearbody E.
unfold cfg_at. change (w64 C1B_V) with (Z_to_bv 64 C1B_V).
aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span W6BB_STRLEN.
- apply (obl_of_range rsegs (w_H W) memc _ C1B_Bx _ _ W6BB_VOCAB 72 Hra).
  + apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
  + rewrite (U_atom _ 10 (W6BB_VOCAB + 8 * j) E10) by (unfold W6BB_VOCAB; lia). lia.
  + rewrite (U_atom _ 10 (W6BB_VOCAB + 8 * j) E10) by (unfold W6BB_VOCAB; lia). lia.
- awr_ok_tac.
- c1b_keep.
  lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
    replace (ss_pc ss) with W6BB_STRLEN by (vm_compute; reflexivity) end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 W6BB_STRLEN) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6BB_STRLEN rg mm md) end.
  apply K.
  + exact HJ.
  + c1b_kio.
  + apply (regs_kept_of_st_ok rsegs _ _ _ regs [w64 (w6bb_vptr j)] (w_H W) c1bv_clob HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + c1b_regv HS (1%bv : bv 5). reflexivity.
  + c1b_regv HS (10%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + c1b_regv HS (25%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + exact KE.
Qed.

(* ---- 0x81900 .. the strlen wrapper's entry ---- *)
Lemma c1b_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c pp kd : Z)
  (r : list byte) (Q : world rsegs -> config -> Prop),
  w6bb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6bb_in B W memc regs R F c pp kd r ->
  kd mod 10 = 1 ->
  w6bb_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1b_hclob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1B_RSTR -> getr regs1 10 = w64 (w6bb_vptr (c1b_j r)) -> getr regs1 25 = w64 (w6bb_vptr (c1b_j r)) ->
    getr regs1 26 = w64 (c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x70 <= a < R + 0x78 \/ R + 0x128 <= a < R + 0x130) ->
      aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x70) 8 (Z.of_nat (length (snd (fuzz_u8 r)))) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x128) 8 (c1b_s6 kd mod 2 ^ 64) ->
    SRr rsegs W (cfg_at rsegs W6BB_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs W6BB_D1 regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r Q Hctx Hin Hkmod Hvoc K.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H20 & H19 & H18 & H26 & H22 & H6 & H16 & H13 & V58 & V100 & V130 & V150 & V158 &
  Hkd & Hpp & Hpp2 & HF4 & HF5 & HF32 & HFapp & Hez & Hera & Hehu & Hc1 & Hinp).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs. pose proof LAWS as HL.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HRb : 0x7fff7f800000 <= R /\ R + 0x220 <= 2 ^ 47) by lia.
destruct Hinp as (Hg & Hrain & Hc0 & Hcr & Ham & Hrhu & Hdis).
pose proof (H13 ltac:(lia)) as H13'. clear H13.
pose proof (c1b_s6_range kd Hkd) as Hs6r.
assert (Hs6m : 0 <= c1b_s6 kd mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (U9 : forall extra, bv_unsigned (ew (Ereg regs extra) 9) = R).
{ intros extra. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E13 : forall extra, ew (Ereg regs extra) 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)).
{ intros extra. rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13'. unfold w64, c1b_s6.
  symmetry. apply Z_to_bv_mod64. }
assert (Hcw : forall o, 0 <= o < 0x220 -> writable_at rsegs (mrestrict (w_H W) memc) (R + o)).
{ intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia. }
destruct r as [|b r'].
- (* no byte left: i = 0 *)
  set (E := Ereg regs []).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (HS0 : st_ok rsegs E c1bh_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c1bh_r70.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. subst E. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r128.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. subst E. rewrite U9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1bh_r70, c1bh_r128.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. subst E. rewrite U9.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bh_ss0 ss_facts c1b_shf c1b_fR].
      split; [|split; exact I]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. subst E. rewrite U9. change (2 ^ 4) with 16. lia.
      + apply (c1b_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS.
  clear HS0.
  assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  assert (E13E : ew E 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)) by (subst E; apply E13).
  clearbody E.
  unfold cfg_at. change (w64 W6BB_D1) with (Z_to_bv 64 W6BB_D1).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span C1B_V.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  (* the bytes outside the spill cells are kept; the cells hold 0 and the kind byte *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x70 <= a < R + 0x78 \/ R + 0x128 <= a < R + 0x130) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1bh_ss0 In] in Hin; destruct Hin as [<-|[<-|[]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1bh_r70 c1bh_r128] in Hr; rewrite UE9 in Hr; lia |];
  assert (VS70 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x70) 8 0);
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rtsb_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rtsb_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x70 (CVal 8 (SLit 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x70 8 (SLit 0) 0 Hc ltac:(reflexivity) ltac:(lia) ltac:(cbn; lia))
    end |];
  assert (VS128 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x128) 8 (c1b_s6 kd mod 2 ^ 64));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r0 with Some ?rg =>
      pose proof (rtsb_region_nth Ef ss ms 1 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rtsb_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x128 (CVal 8 (SOff 13 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x128 8 (SOff 13 0) _ Hc
        ltac:(apply rtsb_den_atom; [rewrite ?ew_ewset_other by lia; exact E13E | exact Hs6m]) ltac:(exact Hs6m) ltac:(cbn; lia))
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1B_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1B_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1B_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) c1bh_rclob HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 c);
  [ c1b_regv HS (26%bv : bv 5); rewrite E18, Z.add_0_r, unsigned_lit_small by lia; reflexivity |];
  apply (c1b_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) 0 Q HJ)
  end.
  + c1b_regv HS (10%bv : bv 5). reflexivity.
  + lia.
  + rewrite RK by c1b_out. exact H20.
  + apply (c1b_vocab_lowk W memc); [|exact Hvoc].
    apply (c1b_lowk_of W memc _ (fun a => R + 0x70 <= a < R + 0x78 \/ R + 0x128 <= a < R + 0x130) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G25 Hm1.
    apply K; cbn [fuzz_u8 fst snd length Z.of_nat].
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1b_kio.
    * intros rg Hr0 Hn.
      rewrite (Hk1 rg Hr0 (c1b_incl_sub c1bv_clob c1b_hclob rg ltac:(intros x Hx; cbn [In c1bv_clob c1b_hclob] in *; tauto) Hn)).
      apply RK; [exact Hr0|]. intros X. apply Hn. cbn [In c1bh_rclob c1b_hclob] in *. tauto.
    * exact G1.
    * exact G10.
    * exact G25.
    * rewrite Hk1 by c1b_out. rewrite R26. unfold w64. f_equal. lia.
    * intros a Ha Hn. rewrite Hm1. exact (KR a Ha Hn).
    * apply (rtsb_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x70) 8); [intros q Hq; apply Hm1|]. exact VS70.
    * apply (rtsb_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x128) 8); [intros q Hq; apply Hm1|]. exact VS128.
- (* a byte m = b, the rest r' *)
  cbn [fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : ~ (R + 0x58 <= c < R + 0x148)) by (destruct (Hdis c ltac:(lia)) as (_ & Hd & _); exact Hd).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  set (E := Ereg regs [w64 m]).
  assert (E6 : ew E 6 = Z_to_bv 64 (n + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E22 : ew E 22 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  assert (E26 : ew E 26 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
  assert (E32 : ew E 32 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  assert (E13E : ew E 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)) by (subst E; apply E13).
  assert (HS0 : st_ok rsegs E c1bh_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold region_ok, c1bh_r70.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r128.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_rI.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E18, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 32 0) m);
          [apply rtsb_den_atom; [exact E32 | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1bh_r70, c1bh_r128, c1bh_rI.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UE9, E18, !unsigned_lit_small by lia.
      split; [split; [lia | split; [lia | exact I]] | split; [split; [lia | exact I] | split; exact I]].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bh_ss1 ss_facts c1bh_facts1 c1b_shf c1b_fR].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UE9. change (2 ^ 4) with 16. lia.
      + apply (c1b_af _ _ _ _ _ _ E20); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E22); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E18); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E32); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  (* a6 = 1, the left side of the T1 test *)
  pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H16; reflexivity)) as HS.
  clear HS0.
  assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs [w64 m]) E) by (subst E; apply env_agree_refl).
  clearbody E.
  unfold cfg_at. change (w64 W6BB_D1) with (Z_to_bv 64 W6BB_D1).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span C1B_V.
  { apply (obl_of_range rsegs (w_H W) memc _ C1B_Bx _ _ c n Hrain).
    - apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x70 <= a < R + 0x78 \/ R + 0x128 <= a < R + 0x130) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn'; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1bh_ss1 In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1bh_r70 c1bh_r128 c1bh_rI] in Hr; rewrite ?UE9, ?E18 in Hr;
    [lia | lia | lia] |];
  assert (VS70 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x70) 8 (Z.of_nat (length r')));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rtsb_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rtsb_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x70 (CVal 8 (SOff 6 (-2)))) ltac:(cbn; tauto)) as Hc;
      refine (val_of_chunk_ok rsegs Ef _ R 0x70 8 (SOff 6 (-2)) (Z.of_nat (length r')) Hc _ ltac:(lia) ltac:(cbn; lia));
      apply bv_eq; rewrite denot_SOff; rewrite ?ew_ewset_other by lia; rewrite E6;
      rewrite !unsigned_lit_small by lia; rewrite zcanon_id by (unfold M64; lia); lia
    end |];
  assert (VS128 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x128) 8 (c1b_s6 kd mod 2 ^ 64));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r0 with Some ?rg =>
      pose proof (rtsb_region_nth Ef ss ms 1 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rtsb_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x128 (CVal 8 (SOff 13 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x128 8 (SOff 13 0) _ Hc
        ltac:(apply rtsb_den_atom; [rewrite ?ew_ewset_other by lia; exact E13E | exact Hs6m]) ltac:(exact Hs6m) ltac:(cbn; lia))
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1B_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1B_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1B_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [w64 m] (w_H W) c1bh_rclob HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 (c + 1));
  [ c1b_regv HS (26%bv : bv 5); rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; lia |];
  assert (R10 : getr (ms_regs ms) 10 = w64 (W6BB_VOCAB + 8 * (m mod 9)));
  [ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS);
    replace (sr_get (ss_regs ss) (10%bv : bv 5)) with c1bh_a0 by (vm_compute; reflexivity);
    apply c1bh_a0_val; [rewrite ?ew_ewset_other by lia; exact E32 | exact Hmb] |];
  apply (c1b_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) (m mod 9) Q HJ R10)
  end.
  + apply Z.mod_pos_bound. lia.
  + rewrite RK by c1b_out. exact H20.
  + apply (c1b_vocab_lowk W memc); [|exact Hvoc].
    apply (c1b_lowk_of W memc _ (fun a => R + 0x70 <= a < R + 0x78 \/ R + 0x128 <= a < R + 0x130) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G25 Hm1.
    apply K.
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1b_kio.
    * intros rg Hr0 Hn'.
      rewrite (Hk1 rg Hr0 (c1b_incl_sub c1bv_clob c1b_hclob rg ltac:(intros x Hx; cbn [In c1bv_clob c1b_hclob] in *; tauto) Hn')).
      apply RK; [exact Hr0|]. intros X. apply Hn'. cbn [In c1bh_rclob c1b_hclob] in *. tauto.
    * exact G1.
    * unfold c1b_j. cbn [fuzz_u8 fst]. exact G10.
    * unfold c1b_j. cbn [fuzz_u8 fst]. exact G25.
    * cbn [fuzz_u8 snd]. rewrite Hk1 by c1b_out. rewrite R26. unfold w64. f_equal. lia.
    * intros a Ha Hn'. rewrite Hm1. exact (KR a Ha Hn').
    * cbn [fuzz_u8 snd]. apply (rtsb_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x70) 8); [intros q Hq; apply Hm1|].
      exact VS70.
    * apply (rtsb_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x128) 8); [intros q Hq; apply Hm1|]. exact VS128.
Qed.
End d.
End b.

Print Assumptions c1b_vload.
Print Assumptions c1b_head.
