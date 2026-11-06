(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the middle of ent_build's
   case 1 (pod.h:287, 211-213, ent_text's clamp) inside LLVMFuzzerTestOneInput, from the strlen wrapper's return
   0x81a6c to __asan_memcpy's entry 0x51860. Proves no function (kind: segment lemma).
   THE CODE:
     0x81a6c  a1 := 0x5f; s8 := a0; s7 := a0; bltu a0,a1 -> 0x81a80; s7 := 0x5f   l = min(len, 95)
     0x81a80  ld s9,0x108(s1) (= F + 0xf8 = e.body); a0 := s9; a1 := s11 (the string); a2 := s7
     0x81a90  jal __asan_memcpy 0x51860 (ra = 0x81a94)
   HOW. One engine run over the cell [R+0x108] (a region based at s1 whose value is F + 0xf8, F the extra env slot
   32); a0 (the length, 12 .. 18 for every vocab string: lib/A/RtPgW6bC1Kit.v c1_len_range) carries that range as a
   fact, which decides the clamp: it never cuts. *)
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

(* [R+0x108] = F + 0xf8 (slot 32 = F); a0 = l in [12, 18] *)
Definition c1m_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 32 0xf8))].
Definition c1m_ss : sstate := mkSS C1_RSTR sr_atoms [c1m_rR] None (mkFacts [c1_fR; (10%nat, mkAF 12 18 0)] [] []).
Definition c1m_clob : list (bv 5) := [1; 10; 11; 12; 23; 24; 25]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

Lemma c1_mid : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F l x : Z)
  (Q : world rsegs -> config -> Prop),
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1e0 <= 2 ^ 47 -> R mod 16 = 0 ->
  getr regs 10 = w64 l -> 12 <= l <= 18 -> getr regs 27 = w64 x ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (F + 0xf8) -> 4096 <= F -> F + 512 <= 2 ^ 47 ->
  (forall regs1 mem1 md1,
    ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k -> same_io mdc md1 ->
    (forall rg : bv 5, bv_unsigned rg <> 0 -> ~ In rg c1m_clob -> getr regs1 rg = getr regs rg) ->
    getr regs1 1 = w64 C1_RCPY -> getr regs1 10 = w64 (F + 0xf8) -> getr regs1 11 = w64 x -> getr regs1 12 = w64 l ->
    getr regs1 23 = w64 l -> getr regs1 24 = w64 l -> getr regs1 25 = w64 (F + 0xf8) ->
    (forall a, aview rsegs (w_H W) mem1 a = aview rsegs (w_H W) memc a) ->
    SRr rsegs W (cfg_at rsegs W6B_MEMCPY regs1 mem1 md1) Q) ->
  SRr rsegs W (cfg_at rsegs C1_RSTR regs memc mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F l x Q HJ H9 HR0 HR1 HR16 H10 Hl H27 V108 HF0 HF1 K.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs. pose proof LAWS as HL.
set (E := Ereg regs [w64 F]).
assert (U9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia. }
assert (E10 : ew E 10 = Z_to_bv 64 l) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E27 : ew E 27 = Z_to_bv 64 x) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (HS : st_ok rsegs E c1m_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_RSTR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, c1m_rR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0x108 8 (SOff 32 0xf8) (F + 0xf8)).
    + apply bv_eq. rewrite denot_SOff, E32. rewrite !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + exact V108.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok c1m_ss ss_facts c1_fR].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 4) with 16. lia.
    + apply (c1_af _ _ _ _ _ _ E10); [lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]. }
assert (HAE : env_agree 32 (Ereg regs [w64 F]) E) by (subst E; apply env_agree_refl).
assert (KE : forall a, aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by reflexivity.
clearbody E.
unfold cfg_at. change (w64 C1_RSTR) with (Z_to_bv 64 C1_RSTR).
aj_run_to w6_tbl_ok HS HJ W6B_MEMCPY.
{ awr_ok_tac. }
c1_keep.
lazymatch goal with HS : st_ok _ _ ?ss (restrict _ ?ms) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl);
  replace (ss_pc ss) with W6B_MEMCPY by (vm_compute; reflexivity) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 W6B_MEMCPY) mm (seg_rom rsegs)) md) with (cfg_at rsegs W6B_MEMCPY rg mm md) end.
lazymatch goal with HS : st_ok _ ?Ef ?ss (restrict _ ?ms) |- _ =>
apply K;
[ exact HJ
| c1_kio
| apply (regs_kept_of_st_ok rsegs _ _ ms regs [w64 F] (w_H W) c1m_clob HS); [env_agree_chain HAE | vm_compute; reflexivity]
| c1_regv HS (1%bv : bv 5); reflexivity
| c1_regv HS (10%bv : bv 5); rewrite E32, unsigned_lit_small by lia; reflexivity
| c1_regv HS (11%bv : bv 5); rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E27; reflexivity
| c1_regv HS (12%bv : bv 5); rewrite E10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
| c1_regv HS (23%bv : bv 5); rewrite E10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
| c1_regv HS (24%bv : bv 5); rewrite E10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity
| c1_regv HS (25%bv : bv 5); rewrite E32, unsigned_lit_small by lia; reflexivity
| exact KE ]
end.
Qed.
End d.
End b.

Print Assumptions c1_mid.
