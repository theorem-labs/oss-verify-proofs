From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK00 YK0c YK0e YK09 YA01 YA0c YA0e YA02 YA03 YA0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h.
Import ListNotations. Import AX2. Import AX2S. Import APG. Import APSG.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* plugin-hostd/fuzz_command's B/StartStkAuxG.v, with this unit's module paths and its ASan+UBSan image's hull top
   0x5fc000 (B/YB12.v img_hi).
   At a hand-off state ch of the start-up certificate at CONFIG_RSEQ flag r whose knowledge covers the auxv vector and
   the 16 AT_RANDOM bytes of the flag-r layout (stk_aux_chk r ch = true: YK09.init_kn_with's KUnk over the vector
   and KBlob over the random bytes, kept to the hand-off), those bytes are present in the hand-off memory.  They are
   the bytes of the entry stack block above the entry sp + 24 that argH0 leaves out (Reusable/YA02.v
   argH0_false_cases); the auxv's 27 or 29 pairs are YK09.AUXSZ r bytes from e_auxb, the random bytes 16 from
   e_atrb r. *)
Definition stk_aux_chk (r : Z) (ch : acs) : bool :=
(kn_vis TFIB ch (fst e_auxb) (snd e_auxb) (AUXSZ r) && kn_vis TFIB ch (fst (e_atrb r)) (snd (e_atrb r)) 16)%bool.
Lemma snd_auxb : snd e_auxb = 24.
Proof. vm_compute. reflexivity. Qed.
Lemma stk_aux_rom_none : forall z, 0x5fc000 <= z < 2 ^ 64 -> YK11.seg_rom TSEGS (Z_to_bv 64 z) = None.
Proof.
intros z Hz. apply seg_rom_none_of_find. apply tfib_in_hull.
rewrite u64_lit by lia. unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
change (img_hi TFIB) with 0x5fc000. lia.
Qed.
Section s.
Variables (TOP : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (fs : Fs.Fs)
(E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model) (r : Z).
Hypothesis HC : cs_ok TSEGS TFIB YA02.LIMIT TOP SINV argH fs E ch R FULL model.
Hypothesis Hchk : stk_aux_chk r ch = true.
(* A byte a known region covers, above the image, is present in the hand-off memory. *)
Lemma vis_present : forall rb rk len, kn_vis TFIB ch rb rk len = true -> forall i, 0 <= i < len ->
0x5fc000 <= uE E rb + rk + i < 2 ^ 64 -> FULL (Z_to_bv 64 (uE E rb + rk + i)) <> None.
Proof.
intros rb rk len Hv i Hi Hr.
pose proof (ho_vis_range TSEGS TFIB YA02.LIMIT TOP SINV argH fs tfib_in_hull tfib_hull_ok E ch R FULL model HC rb rk len Hv i Hi) as Hh.
unfold hreader, mbyte in Hh.
destruct (Mr TFIB TOP argH E ch model FULL (Z_to_bv 64 (uE E rb + rk + i))) as [bb|] eqn:Em.
- rewrite (ho_Mr_full _ _ _ _ _ _ _ _ _ Em). discriminate.
- rewrite (stk_aux_rom_none _ Hr) in Hh. exfalso. apply Hh. reflexivity.
Qed.
(* The auxv vector: [uE E (fst e_auxb) + 24, + AUXSZ r). *)
Lemma stk_auxv_present : forall a, uE E (fst e_auxb) + 24 <= a < uE E (fst e_auxb) + 24 + AUXSZ r ->
0x5fc000 <= a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha Hr. apply andb_prop in Hchk as [H1 _]. rewrite snd_auxb in H1.
replace a with (uE E (fst e_auxb) + 24 + (a - uE E (fst e_auxb) - 24)) by lia.
apply (vis_present _ _ _ H1); lia.
Qed.
(* The random bytes: [uE E (fst (e_atrb r)) + snd (e_atrb r), + 16). *)
Lemma stk_atr_present : forall a, uE E (fst (e_atrb r)) + snd (e_atrb r) <= a < uE E (fst (e_atrb r)) + snd (e_atrb r) + 16 ->
0x5fc000 <= a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha Hr. apply andb_prop in Hchk as [_ H2].
replace a with (uE E (fst (e_atrb r)) + snd (e_atrb r) + (a - uE E (fst (e_atrb r)) - snd (e_atrb r))) by lia.
apply (vis_present _ _ _ H2); lia.
Qed.
End s.
