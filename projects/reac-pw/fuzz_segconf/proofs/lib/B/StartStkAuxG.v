From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.reac_pw.fuzz_segconf.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK11.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB12 YB1h.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* LPS 727298f3 (StackLayout at 75d69e00): the entry block holds, above the envp array, the auxv vector
   ([AUXSZ r] bytes from [e_auxv]: 27 pairs, 29 with CONFIG_RSEQ), the 8-byte STACK_ROUND gap, the 16
   AT_RANDOM bytes at [e_atrandom r], the arch_align_stack pad and the strings.  YA02's [argH0] pins every one
   of those bytes except the auxv and AT_RANDOM ones (YA02.argH0_false_den).  At a hand-off state ch of the
   start-up certificate whose knowledge covers those two ranges ([stk_aux_chk r ch = true]; every hand-off
   state of A/AB01r.v at its own flag does, StartStkAux.tfib_holes_stkaux), their bytes are present in the
   hand-off memory.  The check is [kn_vis] over the two ranges at the addresses the start-up knowledge names
   them by (YK09's [auxt_all] KUnk and [atr_entry] KBlob). *)
Definition stk_aux_chk (r : Z) (ch : acs) : bool :=
(kn_vis TFIB ch (fst e_auxb) (snd e_auxb) (AUXSZ r)
 && kn_vis TFIB ch (fst (e_atrb r)) (snd (e_atrb r)) 16)%bool.
Lemma stk_aux_rom_none : forall z, 0x602000 <= z < 2 ^ 64 -> YK11.seg_rom TSEGS (Z_to_bv 64 z) = None.
Proof.
intros z Hz. apply seg_rom_none_of_find. apply tfib_in_hull.
rewrite u64_lit by lia. unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
change (img_hi TFIB) with 0x602000. lia.
Qed.
Section s.
Variables (LIM TOP : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (r : Z).
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH FS0 E ch R FULL model.
Hypothesis Hchk : stk_aux_chk r ch = true.
Lemma stk_aux_present : forall a,
(uE E (fst e_auxb) + snd e_auxb <= a < uE E (fst e_auxb) + snd e_auxb + AUXSZ r)
\/ (uE E (fst (e_atrb r)) + snd (e_atrb r) <= a < uE E (fst (e_atrb r)) + snd (e_atrb r) + 16) ->
0x602000 <= a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha Hr. pose proof Hchk as Hc. unfold stk_aux_chk in Hc. apply andb_prop in Hc as [H1 H2].
assert (X : hreader TSEGS (Mr TFIB TOP argH E ch model FULL) a <> None).
{ destruct Ha as [Ha|Ha].
- replace a with (uE E (fst e_auxb) + snd e_auxb + (a - uE E (fst e_auxb) - snd e_auxb)) by lia.
  apply (ho_vis_range TSEGS TFIB LIM TOP SINV argH FS0 tfib_in_hull tfib_hull_ok E ch R FULL model HC _ _ _ H1). lia.
- replace a with (uE E (fst (e_atrb r)) + snd (e_atrb r) + (a - uE E (fst (e_atrb r)) - snd (e_atrb r))) by lia.
  apply (ho_vis_range TSEGS TFIB LIM TOP SINV argH FS0 tfib_in_hull tfib_hull_ok E ch R FULL model HC _ _ _ H2). lia. }
unfold hreader, mbyte in X.
destruct (Mr TFIB TOP argH E ch model FULL (Z_to_bv 64 a)) as [bb|] eqn:Em.
- rewrite (ho_Mr_full _ _ _ _ _ _ _ _ _ Em). discriminate.
- rewrite (stk_aux_rom_none _ Hr) in X. exfalso. apply X. reflexivity.
Qed.
End s.
