(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_h_model.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma idx2_val : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.shiftl s 32 mod 18446744073709551616) 31 = 2 * s.
Proof.
intros s Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0040=17303709668.941201450270.244015170411.27224926811.2 00000600:00;00<S1H2H0S2HsSS".
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
change (2^32) with 4294967296. change (2^31) with 2147483648.
rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma idx2_val' : forall s, 0 <= s < 2147483648 -> Z.shiftr (Z.land (Z.shiftl s 32) 18446744073709551615) 31 = 2 * s.
Proof.
intros s Hs. change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0010=35497641323.2000001S".
rewrite Z.land_ones by lia.
change (2^64) with 18446744073709551616. apply idx2_val. exact Hs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Cmp.
Variables (gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : fmem) (SP NC RT : Z) (nc rt : list Z) (msv : Z).
Variable POST : machine_state -> Prop.
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis LNC : length nc = 256%nat.
Hypothesis LRT : length rt = 256%nat.
Hypothesis NCB : bytes_at psegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis RTB : bytes_at psegs m RT (u16s (map (Z_to_bv 64) rt)).
Hypothesis AGREE : forall i, 0 <= i <= msv -> Znth i rt = Znth i nc.
Hypothesis MI : mem_inv psegs m.
Hypothesis NCR : 0 <= NC /\ NC + 512 < 2^64.
Hypothesis RTR : 0 <= RT /\ RT + 512 < 2^64.
Notation STpc pc x1 x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 s0 (Z_to_bv 64 msv) x10 (Z_to_bv 64 NC) (Z_to_bv 64 RT) x13 x14 x15 x16 x17
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
#[using="nc rt MSV LNC LRT NCB RTB AGREE"] Lemma cmp_loop : forall f s (x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
0 <= s <= msv -> msv - s < Z.of_nat f ->
(forall (y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
evt psegs POST (STpc 0x13710 y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 y31)) ->
evt psegs POST (STpc 0x136ec x1 x5 x6 x7 (Z_to_bv 64 s) x13 x14 x15 x16 x17 x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros s x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 HS HF K.
{ exfalso. cbn in HF. Local Ltac2 Set LiaHints.tbl := fun () => "00A0>11449825958.7711868199092.5411869970069.531304312773.58 1626025075.55 18606756865.6218606756868.5525684708034.5131827797969.5638903008788.5142134489428.5543324722563.635468053843.56 59314923118.4965453664584.5267148971104.567604148560.56 00000100@00O00P00c01601A01L01X01g02302402F02M02`03303CFS3LNC3LRT2HS2HFS3LNC3LRT2HS2HFFS3MSV3LNC3LRT2HS2HFS3MSV3LNC3LRT2HS2HFS3MSV2HS2HFS3MSV2HS2HFS3LNC3LRT2HFS3MSV3LNC2HS2HFS3LNC3LRT2HFFS3LNC3LRT2HS2HF2B2S2HS2HFS3MSV3LNC3LRT2HS2HFS3MSV3LNC3LRT2HS2HFS3MSV3LNC3LRT2HF".
lia. }
zstep. zstep.
first [rewrite idx2_val by lia | rewrite idx2_val' by lia].
zstep. zstep.
assert (NTHN : nth_error (map (Z_to_bv 64) nc) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. unfold Znth. rewrite (nth_error_nth' nc 0) by lia. reflexivity. }
assert (NTHR : nth_error (map (Z_to_bv 64) rt) (Z.to_nat s) = Some (Z_to_bv 64 (Znth s nc))).
{ rewrite nth_error_map. rewrite <- (AGREE s HS). unfold Znth. rewrite (nth_error_nth' rt 0) by lia. reflexivity. }
pose proof (u16ro_read psegs m NC _ s _ (wa (NC + 2 * s)) NCB NTHN ltac:(lia) eq_refl) as RD1.
pose proof (u16ro_read psegs m RT _ s _ (wa (RT + 2 * s)) RTB NTHR ltac:(lia) eq_refl) as RD2.
zstep.
zstep.
zstep. if_cases B. { exfalso. revert B. rewrite bv_eqb_refl. discriminate. }
clear B.
zstep. sw32 (s + 1).
zstep. if_cases B2; zify_cond B2.
- eapply (IH (s + 1)); [lia| lia| exact K].
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Cmp.
