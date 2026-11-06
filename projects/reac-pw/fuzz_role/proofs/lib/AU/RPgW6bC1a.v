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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC1Mid.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the pcs, the registers (the string in s9, l in s2 and s6, e62.body in s8) and the cell
   [R+0x130] (= F + 0x218, e62.body) are image B's; the prefix c1_ becomes c1b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC1HeadB.v and
   proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC1MidB.v at a191d52e2a9a for reac-pw/fuzz_role's image B
   (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and RPgCSpec, lib/AU/RPgSteps.v rl_
   names); the two files are one; every pc, register and real-frame cell is role B's: the head reads e62.body from
   [R+0x110] into s10 (one more read-only cell, slot 32; the index byte moves to slot 33), the shadow offset is s11,
   the T1 tests' 1 is s4 (pinned), the kind byte's address a6; it spills the cursor (a6) to [R+0x58] and the kind byte
   to [R+0x118]; the load block moves what is left from t1 to s4 and the string to s6; the middle reads no cell
   (e62.body is s10, l goes to s2 and s8). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the head and the middle of
   ent_build's case 1 (pod.h:286-287, 211-213, ent_text's clamp) inside LLVMFuzzerTestOneInput (0x80020), from the
   case entry 0x810d0 to the strlen wrapper's entry 0x41b60, and from its return 0x813f4 to checked_memcpy's entry
   0x5116c. Proves no function (kind: segment lemma).
   THE CODE (registers as lib/AU/RPgW6bBase.v w6bb_in: s1 = R, s11 = SHADOW_OFF, s2 = c, a6 = c - 1, s6 = |r|,
   t1 = |r| + 1, s4 = 1, a3 = the kind byte sign-extended):
     0x810d0  beqz s6 -> 0x813b4                     no byte left: i = 0
     0x810d4  a0 := s2 + 1; 0x810d8 ld s10,0x110(s1) (= F + 0x218, e62.body); 0x810dc bltu s4,a0 (T1; else the
              `unimp` 0x82604 through 0x810e0)
     0x810e4 .. 0x810f0  the instrumented check of s2 (NE-SLOW, slow block 0x81ac8; its error path 0x828b4)
     0x810f4  lbu a1,0(s2); a0 := 0x9a7a0; 0x81100 .. 0x8111c a1 := 8 (i % 9) (mul 0x39, srli 9, subw, zext.b)
     0x81120  a2 := ~a0; 0x81124 bgeu a2,a1 (T2; else the `unimp` through 0x81128); t1 := t1 - 2; a6 := a6 + 2;
              a0 := a0 + a1; j 0x813c8
     0x813b4  t1 := 0; a0 := 0x9a7a0; a6 := s2; ld s10,0x110(s1)
     0x813c8  sd a6,0x58(s1); sd a3,0x118(s1)                  (c1b_head, both arms, to 0x813d0)
     0x813d0 .. 0x813e0  the instrumented check of the 8-byte load (lbu; beqz; else `j` to the error path 0x82854)
     0x813e4  mv s4,t1; ld s6,0(a0); mv a0,s6; 0x813f0 jal 0x41b60 (ra = 0x813f4)    (c1b_vload)
     0x813f4  a1 := 0x5f; s8 := a0; s2 := a0; bltu a0,a1 -> 0x81408; s2 := 0x5f   l = min(len, 95)
     0x81408  a0 := s10 (e62.body); a1 := s6 (the string); a2 := s2; 0x81414 jal checked_memcpy 0x5116c
              (ra = 0x81418)                                                     (c1b_mid)
   HOW. c1b_vload: a0 is the register atom x10 (so the engine sees the check's `(x >> 3) + s11` form), the 8-byte
   cell a one-chunk region based at it whose value is the extra env slot 32 (w6bb_vocab_ok gives the cell); the check
   leaves the obligation range_addressable (&vocab[i]) 8, a sub-range of vocab's 72 registered bytes. c1b_head: the
   spill cells [R+0x58, R+0x60) and [R+0x118, R+0x120) two written regions based at s1 (the callers' stack window),
   the cell [R+0x110] a read-only region based at s1 whose value is slot 32 (F + 0x218), the input byte a one-byte
   region based at s2 whose value is slot 33; s4 is pinned to 1 and the cursor (atom 18) carries [1, 2^47 - 1], which
   decides T1 (the trap branch 0x810dc is refuted by the run); the index's range [0, 2040] against the literal ~a0
   decides T2 (0x81124 refuted by the run); the check of s2 leaves range_addressable c 1 (w6bb_inp); the no-byte arm
   pins s6 to 0; a0 at 0x813d0 is checked for all 256 values of the byte (c1bh_a0_val). c1b_mid: one engine run with
   no region; a0 (the length, 12 .. 18 for every vocab string: lib/AU/RPgW6bC1Kit.v c1b_len_range) carries that range
   as a fact, which decides the clamp: it never cuts. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgMem RPgSteps RPgW6bBase RPgW6bC1Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RPgSteps.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ======================================== the entry states ======================================== *)
(* the spill cells [R+0x58, R+0x60) (the cursor) and [R+0x118, R+0x120) (the kind byte), written *)
Definition c1bh_r58 : YP09.region := YP09.mkRegion (Some 9%nat) 0x58 0x60 0x58 0x60 [].
Definition c1bh_r118 : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x120 0x118 0x120 [].
(* the cell [R+0x110] = F + 0x218, e62.body (slot 32), read *)
Definition c1bh_r110 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x110 0x118 0 0 [YP09.mkChunk 0x110 (CVal 8 (SOff 32 0))].
(* the index byte at c (slot 33) *)
Definition c1bh_rI : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition c1bh_facts1 : facts :=
  mkFacts [c1b_fR; c1b_shf; (22%nat, mkAF 1 (2 ^ 47) 0); (18%nat, mkAF 1 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition c1bh_ss1 : sstate := mkSS W6BB_D1 sr_atoms [c1bh_r58; c1bh_r118; c1bh_r110; c1bh_rI] None c1bh_facts1.
Definition c1bh_ss0 : sstate :=
  mkSS W6BB_D1 sr_atoms [c1bh_r58; c1bh_r118; c1bh_r110] None (mkFacts [c1b_fR; c1b_shf] [] []).
(* the vocab cell at a0 (slot 32 = vocab[i]) *)
Definition c1bv_rV : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition c1bv_ss : sstate := mkSS C1B_V sr_atoms [c1bv_rV] None
  (mkFacts [c1b_shf; (10%nat, mkAF W6BB_VOCAB (W6BB_VOCAB + 64) 3)] [] []).
(* the registers each block may change (the head's run: t1, a0, a1, a2, a6, s10, and s4 and s6 pinned; the load
   block: ra, a0, a1, s4, s6) *)
Definition c1bv_clob : list (bv 5) := [1; 10; 11; 20; 22]%bv.
Definition c1bh_rclob : list (bv 5) := [6; 10; 11; 12; 16; 20; 22; 26]%bv.
Definition c1b_hclob : list (bv 5) := [1; 6; 10; 11; 12; 16; 20; 22; 26]%bv.
(* the middle's run: ra, a0, a1, a2, s2, s8 *)
Definition c1bm_ss : sstate := mkSS C1B_RSTR sr_atoms [] None (mkFacts [(10%nat, mkAF 12 18 0)] [] []).
Definition c1bm_clob : list (bv 5) := [1; 10; 11; 12; 18; 24]%bv.

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x813d0 as the engine computes it from the byte (slot 33) *)
Definition c1bh_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 33 0) (SLit 57)) (SLit 9).
Definition c1bh_a0 : sv :=
  SAlu ALU_ADD (SLit 632736)
    (SAlu ALU_SLL
       (SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 33 0) c1bh_q) (SAlu ALU_SLL c1bh_q (SLit 3))) (SLit 255))
       (SLit 3)).
Definition c1b_envz (z : Z) : env := mkEnv (fun _ => Z_to_bv 64 z) (fun _ => []).
Lemma c1bh_a0_val : forall E m, ew E 33 = Z_to_bv 64 m -> 0 <= m < 256 ->
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

(* ---- 0x813d0 .. the strlen wrapper's entry: the checked load of vocab[j] ---- *)
Lemma c1b_vload : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) j
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 (W6BB_VOCAB + 8 * j) -> 0 <= j < 9 -> getr regs 27 = w64 SHADOW_OFF ->
  w6bb_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1bv_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1B_RSTR -> getr regs1 10 = w64 (w6bb_vptr j) -> getr regs1 22 = w64 (w6bb_vptr j) ->
    getr regs1 20 = getr regs 6 ->
    (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6BB_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1B_V regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs j Q HJ H10 Hj H27 (Hra & Hv) K.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
destruct (Hv j Hj) as [Hcell Hcs].
pose proof (c1b_vptr_range j Hj) as Hvp.
set (E := Ereg regs [w64 (w6bb_vptr j)]).
assert (E10 : ew E 10 = Z_to_bv 64 (W6BB_VOCAB + 8 * j)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E6 : ew E 6 = getr regs 6) by (subst E; exact (ew_Ereg_nat regs _ 6 6%bv eq_refl)).
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
    + apply rl_den_atom; [exact E32 | lia].
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact Hcell.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bv_ss ss_facts c1b_shf].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c1b_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
    + apply (c1b_af _ _ _ _ _ _ E10); unfold W6BB_VOCAB; [lia | lia | | lia].
      change (2 ^ 3) with 8. rewrite (Z.mul_comm 8 j). rewrite Z.mod_add by lia. reflexivity. }
assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [w64 (w6bb_vptr j)]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
clearbody E.
unfold cfg_at. change (w64 C1B_V) with (Z_to_bv 64 C1B_V).
aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span W6BB_STRLEN.
- apply (obl_of_range rsegs (w_H W) memc _ C1B_Bx _ _ W6BB_VOCAB 72 Hra).
  + apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
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
  + c1b_regv HS (22%bv : bv 5). rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + c1b_regv HS (20%bv : bv 5). rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + exact KE.
Qed.

(* ---- 0x810d0 .. the strlen wrapper's entry ---- *)
Lemma c1b_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c pp kd : Z)
  (r : list byte) (Q : world rsegs -> config -> Prop),
  w6bb_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6bb_in B W memc regs R F c pp kd r ->
  kd mod 10 = 1 ->
  w6bb_vocab_ok W memc ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1b_hclob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1B_RSTR -> getr regs1 10 = w64 (w6bb_vptr (c1b_j r)) -> getr regs1 22 = w64 (w6bb_vptr (c1b_j r)) ->
    getr regs1 20 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))) -> getr regs1 26 = w64 (F + 0x218) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) ->
      aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x58) 8 (c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))) ->
    val_mem rsegs (mrestrict (w_H W) mem1) (R + 0x118) 8 (c1b_s6 kd mod 2 ^ 64) ->
    SRr rsegs W (cfg_at rsegs W6BB_STRLEN regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs W6BB_D1 regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r Q Hctx Hin Hkmod Hvoc K.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & V48 & Vf0 & V110 & V130 & V140 &
  V158 & Hkd & Hpp & Hpp2 & HF4 & HF5 & HF32 & HFapp & Hez & Hera & Hehu & Hc1 & Hinp).
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
unfold T_SEG_STK, ASTACK in HspR.
assert (HRb : 0x7fff7f800000 <= R /\ R + 0x200 <= 2 ^ 47) by lia.
destruct Hinp as (Hg & Hrain & Hc0 & Hcr & Ham & Hrhu & Hdis).
pose proof (H13 ltac:(lia)) as H13'. clear H13.
pose proof (c1b_s6_range kd Hkd) as Hs6r.
assert (Hs6m : 0 <= c1b_s6 kd mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (U9 : forall extra, bv_unsigned (ew (Ereg regs extra) 9) = R).
{ intros extra. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E13 : forall extra, ew (Ereg regs extra) 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)).
{ intros extra. rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13'. unfold w64, c1b_s6.
  symmetry. apply Z_to_bv_mod64. }
assert (Hcw : forall o, 0 <= o < 0x200 -> writable_at rsegs (mrestrict (w_H W) memc) (R + o)).
{ intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia. }
destruct r as [|b r'].
- (* no byte left: i = 0 *)
  set (E := Ereg regs [w64 (F + 0x218)]).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 (F + 0x218)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  assert (HS0 : st_ok rsegs E c1bh_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold region_ok, c1bh_r58.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r118.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r110.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0x110 8 (SOff 32 0) (F + 0x218));
          [apply rl_den_atom; [exact E32 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact V110].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1bh_r58, c1bh_r118, c1bh_r110.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UE9.
      repeat split; first [exact I | lia].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bh_ss0 ss_facts c1b_shf c1b_fR].
      split; [|split; exact I]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UE9. change (2 ^ 4) with 16. lia.
      + apply (c1b_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H22; reflexivity)) as HS.
  clear HS0.
  assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs [w64 (F + 0x218)]) E) by (subst E; apply env_agree_refl).
  assert (E13E : ew E 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)) by (subst E; apply E13).
  clearbody E.
  unfold cfg_at. change (w64 W6BB_D1) with (Z_to_bv 64 W6BB_D1).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span C1B_V.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  (* the bytes outside the spill cells are kept; the cells hold the cursor and the kind byte *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1bh_ss0 In] in Hin; destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1bh_r58 c1bh_r118 c1bh_r110] in Hr; rewrite UE9 in Hr; lia |];
  assert (VS58 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x58) 8 c);
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rl_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rl_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x58 (CVal 8 (SOff 18 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x58 8 (SOff 18 0) c Hc
        ltac:(apply rl_den_atom; [rewrite ?ew_ewset_other by lia; exact E18 | cbn [length] in Hcr; lia])
        ltac:(cbn [length] in Hcr; lia) ltac:(cbn; lia))
    end |];
  assert (VS118 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x118) 8 (c1b_s6 kd mod 2 ^ 64));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r0 with Some ?rg =>
      pose proof (rl_region_nth Ef ss ms 1 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rl_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x118 (CVal 8 (SOff 13 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x118 8 (SOff 13 0) _ Hc
        ltac:(apply rl_den_atom; [rewrite ?ew_ewset_other by lia; exact E13E | exact Hs6m]) ltac:(exact Hs6m) ltac:(cbn; lia))
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1B_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1B_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1B_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [w64 (F + 0x218)] (w_H W) c1bh_rclob HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 (F + 0x218));
  [ c1b_regv HS (26%bv : bv 5); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
  assert (R6 : getr (ms_regs ms) 6 = w64 0);
  [ c1b_regv HS (6%bv : bv 5); reflexivity |];
  apply (c1b_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) 0 Q HJ)
  end.
  + c1b_regv HS (10%bv : bv 5). reflexivity.
  + lia.
  + rewrite RK by c1b_out. exact H27.
  + apply (c1b_vocab_lowk W memc); [|exact Hvoc].
    apply (c1b_lowk_of W memc _ (fun a => R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G22 G20 Hm1.
    apply K; cbn [fuzz_u8 fst snd length Z.of_nat].
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1b_kio.
    * intros rg Hr0 Hn.
      rewrite (Hk1 rg Hr0 (c1b_incl_sub c1bv_clob c1b_hclob rg ltac:(intros x Hx; cbn [In c1bv_clob c1b_hclob] in *; tauto) Hn)).
      apply RK; [exact Hr0|]. intros X. apply Hn. cbn [In c1bh_rclob c1b_hclob] in *. tauto.
    * exact G1.
    * exact G10.
    * exact G22.
    * rewrite G20. exact R6.
    * rewrite Hk1 by c1b_out. exact R26.
    * intros a Ha Hn. rewrite Hm1. exact (KR a Ha Hn).
    * lazymatch goal with |- val_mem _ _ _ _ ?v => replace v with c by lia end.
      apply (rl_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x58) 8); [intros q Hq; apply Hm1|]. exact VS58.
    * apply (rl_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x118) 8); [intros q Hq; apply Hm1|]. exact VS118.
- (* a byte m = b, the rest r' *)
  cbn [fuzz_u8 fst snd].
  pose proof (Cursor.byte_range b) as Hmb.
  set (m := bv_unsigned b) in *.
  set (n := Z.of_nat (length (b :: r'))) in *.
  assert (Hn : n = Z.of_nat (length r') + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : ~ (R + 0x48 <= c < R + 0x160)) by (destruct (Hdis c ltac:(lia)) as (_ & Hd & _); exact Hd).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  set (E := Ereg regs [w64 (F + 0x218); w64 m]).
  assert (E6 : ew E 6 = Z_to_bv 64 (n + 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact H6).
  assert (E16 : ew E 16 = Z_to_bv 64 (c - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact H16).
  assert (E18 : ew E 18 = Z_to_bv 64 c) by (subst E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
  assert (E22 : ew E 22 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 (F + 0x218)) by (subst E; exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 m) by (subst E; exact (ew_Ereg_extra regs _ 1)).
  assert (UE9 : bv_unsigned (ew E 9) = R) by (subst E; apply U9).
  assert (E13E : ew E 13 = Z_to_bv 64 (c1b_s6 kd mod 2 ^ 64)) by (subst E; apply E13).
  assert (HS0 : st_ok rsegs E c1bh_ss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6BB_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
      + unfold region_ok, c1bh_r58.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r118.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hcw; lia | constructor].
      + unfold region_ok, c1bh_r110.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UE9.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0x110 8 (SOff 32 0) (F + 0x218));
          [apply rl_den_atom; [exact E32 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia
          | exact V110].
      + unfold region_ok, c1bh_rI.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite E18, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 33 0) m);
          [apply rl_den_atom; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | exact Hm0].
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1bh_r58, c1bh_r118, c1bh_r110, c1bh_rI.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UE9, E18, !unsigned_lit_small by lia.
      repeat split; first [exact I | lia].
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bh_ss1 ss_facts c1bh_facts1 c1b_shf c1b_fR].
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UE9. change (2 ^ 4) with 16. lia.
      + apply (c1b_af _ _ _ _ _ _ E27); unfold SHADOW_OFF; [lia | lia | reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E22); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E18); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
      + apply (c1b_af _ _ _ _ _ _ E33); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
  (* s4 = 1, the left side of the T1 test *)
  pose proof (st_ok_pin_lit rsegs _ _ _ (20%bv : bv 5) 1 HS0 eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H20; reflexivity)) as HS.
  clear HS0.
  assert (SHOK : sh_ok rsegs C1B_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 (Ereg regs [w64 (F + 0x218); w64 m]) E) by (subst E; apply env_agree_refl).
  clearbody E.
  unfold cfg_at. change (w64 W6BB_D1) with (Z_to_bv 64 W6BB_D1).
  aj_run_to_tok w6bb_tbl_ok HS HJ SHOK C1B_span C1B_V.
  { apply (obl_of_range rsegs (w_H W) memc _ C1B_Bx _ _ c n Hrain).
    - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia.
    - rewrite (U_atom _ 18 c E18) by lia. lia. }
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite UE9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) ->
    aview rsegs (w_H W) (ms_mem ms) a = aview rsegs (w_H W) memc a);
  [ intros a Ha Hn'; apply (aview_eq_of rsegs); apply HFr; rewrite unsigned_lit_small by exact Ha;
    intros (rg & Hin & Hr); cbn [ss_mem c1bh_ss1 In] in Hin; destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val c1bh_r58 c1bh_r118 c1bh_r110 c1bh_rI] in Hr; rewrite ?UE9, ?E18 in Hr;
    [lia | lia | lia | lia] |];
  assert (VS58 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x58) 8 (c + 1));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 0) in
    lazymatch r0 with Some ?rg =>
      pose proof (rl_region_nth Ef ss ms 0 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rl_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x58 (CVal 8 (SOff 16 2))) ltac:(cbn; tauto)) as Hc;
      refine (val_of_chunk_ok rsegs Ef _ R 0x58 8 (SOff 16 2) (c + 1) Hc _ ltac:(lia) ltac:(cbn; lia));
      apply bv_eq; rewrite denot_SOff; rewrite ?ew_ewset_other by lia; rewrite E16;
      rewrite !unsigned_lit_small by lia; rewrite zcanon_id by (unfold M64; lia); lia
    end |];
  assert (VS118 : val_mem rsegs (mrestrict (w_H W) (ms_mem ms)) (R + 0x118) 8 (c1b_s6 kd mod 2 ^ 64));
  [ let r0 := eval vm_compute in (nth_error (ss_mem ss) 1) in
    lazymatch r0 with Some ?rg =>
      pose proof (rl_region_nth Ef ss ms 1 rg (w_H W) HS ltac:(vm_compute; reflexivity)) as HRR;
      pose proof (rl_chunks Ef _ 9%nat _ _ _ _ _ _ HRR ltac:(rewrite ?ew_ewset_other by lia; exact UE9)
        (YP09.mkChunk 0x118 (CVal 8 (SOff 13 0))) ltac:(cbn; tauto)) as Hc;
      exact (val_of_chunk_ok rsegs Ef _ R 0x118 8 (SOff 13 0) _ Hc
        ltac:(apply rl_den_atom; [rewrite ?ew_ewset_other by lia; exact E13E | exact Hs6m]) ltac:(exact Hs6m) ltac:(cbn; lia))
    end |];
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with C1B_V by (vm_compute; reflexivity)
  end.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 C1B_V) mm (seg_rom rsegs)) md) with (cfg_at rsegs C1B_V rg mm md) end.
  lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms), HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ ?mm) |- _ =>
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs [w64 (F + 0x218); w64 m] (w_H W) c1bh_rclob HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK;
  assert (R26 : getr (ms_regs ms) 26 = w64 (F + 0x218));
  [ c1b_regv HS (26%bv : bv 5); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity |];
  assert (R6 : getr (ms_regs ms) 6 = w64 (Z.of_nat (length r')));
  [ c1b_regv HS (6%bv : bv 5); rewrite E6, unsigned_lit_small by lia; unfold w64; f_equal; lia |];
  assert (R10 : getr (ms_regs ms) 10 = w64 (W6BB_VOCAB + 8 * (m mod 9)));
  [ rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS);
    replace (sr_get (ss_regs ss) (10%bv : bv 5)) with c1bh_a0 by (vm_compute; reflexivity);
    apply c1bh_a0_val; [rewrite ?ew_ewset_other by lia; exact E33 | exact Hmb] |];
  apply (c1b_vload STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W (ms_mem ms) _ (ms_regs ms) (m mod 9) Q HJ R10)
  end.
  + apply Z.mod_pos_bound. lia.
  + rewrite RK by c1b_out. exact H27.
  + apply (c1b_vocab_lowk W memc); [|exact Hvoc].
    apply (c1b_lowk_of W memc _ (fun a => R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) KR). intros a Ha. lia.
  + intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G22 G20 Hm1.
    apply K.
    * exact HJ1.
    * eapply same_io_trans; [|exact Hio1]. c1b_kio.
    * intros rg Hr0 Hn'.
      rewrite (Hk1 rg Hr0 (c1b_incl_sub c1bv_clob c1b_hclob rg ltac:(intros x Hx; cbn [In c1bv_clob c1b_hclob] in *; tauto) Hn')).
      apply RK; [exact Hr0|]. intros X. apply Hn'. cbn [In c1bh_rclob c1b_hclob] in *. tauto.
    * exact G1.
    * unfold c1b_j. cbn [fuzz_u8 fst]. exact G10.
    * unfold c1b_j. cbn [fuzz_u8 fst]. exact G22.
    * cbn [fuzz_u8 snd]. rewrite G20. exact R6.
    * rewrite Hk1 by c1b_out. exact R26.
    * intros a Ha Hn'. rewrite Hm1. exact (KR a Ha Hn').
    * cbn [fuzz_u8 snd]. lazymatch goal with |- val_mem _ _ _ _ ?v => replace v with (c + 1) by lia end.
      apply (rl_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x58) 8); [intros q Hq; apply Hm1|]. exact VS58.
    * apply (rl_val_kept (w_H W) (ms_mem ms) mem1 (R + 0x118) 8); [intros q Hq; apply Hm1|]. exact VS118.
Qed.

(* ---- 0x813f4 .. checked_memcpy's entry: l = min(len, 95), the copy's arguments ---- *)
Lemma c1b_mid : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (F l x : Z)
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 l -> 12 <= l <= 18 -> getr regs 22 = w64 x -> getr regs 26 = w64 (F + 0x218) ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1bm_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1B_RCPY -> getr regs1 10 = w64 (F + 0x218) -> getr regs1 11 = w64 x -> getr regs1 12 = w64 l ->
    getr regs1 18 = w64 l -> getr regs1 24 = w64 l ->
    (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6BB_MEMCPY regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1B_RSTR regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs F l x Q HJ H10 Hl H22 H26 K.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
set (E := Ereg regs []).
assert (E10 : ew E 10 = Z_to_bv 64 l) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E22 : ew E 22 = Z_to_bv 64 x) by (subst E; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 (F + 0x218)) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (HS : st_ok rsegs E c1bm_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1B_RSTR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1bm_ss ss_facts].
    split; [|split; exact I]. split; [|exact I].
    apply (c1b_af _ _ _ _ _ _ E10); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
clearbody E.
unfold cfg_at. change (w64 C1B_RSTR) with (Z_to_bv 64 C1B_RSTR).
aj_run_to w6bb_tbl_ok HS HJ W6BB_MEMCPY.
{ awr_ok_tac. }
c1b_keep.
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with W6BB_MEMCPY by (vm_compute; reflexivity) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 W6BB_MEMCPY) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6BB_MEMCPY rg mm md) end.
lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms) |- _ =>
apply K;
[ exact HJ
| c1b_kio
| apply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) c1bm_clob HS); [env_agree_chain HAE | vm_compute; reflexivity]
| c1b_regv HS (1%bv : bv 5); reflexivity
| c1b_regv HS (10%bv : bv 5); rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1b_regv HS (11%bv : bv 5); rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1b_regv HS (12%bv : bv 5); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1b_regv HS (18%bv : bv 5); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| c1b_regv HS (24%bv : bv 5); rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| exact KE ]
end.
Qed.
End d.
End b.
