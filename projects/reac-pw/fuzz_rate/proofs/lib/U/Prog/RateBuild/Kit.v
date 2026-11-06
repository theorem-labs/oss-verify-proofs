(** Lemmas of the record and the selector that several pieces of the UBSan builder walk share (Key, Struct, Int7,
    Shape7, Pre): image-independent, from reac-pw/fuzz_role's U/Prog/RoleBuild/Key.v, kept apart here so the pieces can be walked in parallel. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import Facts Cut.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Import ListNotations.
Open Scope Z_scope.

(** The bytes the key's put32 stores (the key is below 2^24, so its top byte is the stored zero). *)
Lemma key_bytes : forall sel,
  le1 (Z_to_bv 64 (key_of sel)) ++ le1 (Z_to_bv 64 (Z.shiftr (key_of sel mod 18446744073709551616) 8))
  ++ le1 (Z_to_bv 64 (Z.shiftr (key_of sel mod 18446744073709551616) 16)) ++ le1 (Z_to_bv 64 0)
  = le32 (key_of sel).
Proof. intros sel. unfold key_of. destruct (sel mod 4 =? 0); vm_compute; reflexivity. Qed.

Lemma pc_buf_cap : forall sh ps, pc_wf sh ps -> (length ps <= 2)%nat ->
  Z.of_nat (length (pc_buf (PbCut sh ps None))) <= 3632 /\ (8 | Z.of_nat (length (pc_buf (PbCut sh ps None)))).
Proof.
  intros sh ps (_ & Hv & He & _) Hp.
  assert (Hv' : Forall (fun kv => pval_wf (snd kv)) ps)
    by (eapply Forall_impl; [|exact Hv]; intros kv [_ H]; exact H).
  destruct (pc_buf_len_none sh ps Hv' He) as [H D]. split; [lia | exact D].
Qed.

Lemma land3 : forall z, Z.land z 3 = z mod 4.
Proof. intros z. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
