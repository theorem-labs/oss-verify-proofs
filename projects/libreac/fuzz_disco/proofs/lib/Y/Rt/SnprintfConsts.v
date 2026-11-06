From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YG0n YG0d YM05 YB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition disco_fmt_lo : Z := 0x102e0.
Definition disco_fmt_hi : Z := 0x22fac.
Definition snp_cr : list (Z * Z) :=
[(0x15288, 7); (0x1b2a2, 6); (0x14097, 5); (0x199e7, 3);
(0x10806, 4); (0x139e5, 3); (0x162d9, 9); (0x1c3d1, 8);
(0x10330, 8); (0x103f8, 8); (0x229a0, 464); (0x22858, 224);
(0x22b70, 16); (0x22958, 72); (0x10b7c, 1); (0x10368, 32)].
Lemma snp_cr_bounds : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) snp_cr.
Proof.
assert (H : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? 2 ^ 63)) snp_cr = true) by reflexivity.
apply Forall_forall. intros r Hr. eapply forallb_forall in H; [|exact Hr].
apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
Lemma snp_cr_in_rom : forall a, Exists (in_zr a) snp_cr -> in_rom tfibsegs a.
Proof.
intros a Ha.
assert (E : existsb (fun s : Segment => negb (seg_writable s) && forallb (fun r =>
  (Z.of_N (seg_base s) <=? fst r) && (fst r + snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) snp_cr) tfibsegs = true)
  by (vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hin & Hb). apply andb_true_iff in Hb as [Hw Hf].
apply Exists_exists in Ha as (r & Hr & Ha). eapply forallb_forall in Hf; [|exact Hr].
apply andb_true_iff in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
unfold in_zr in Ha. unfold in_rom. exists sg. split; [exact Hin|].
split; [destruct (seg_writable sg); [discriminate | reflexivity] | lia].
Qed.
Section c. Context {rc : YM05.RunCeil}.
Lemma snp_consts_of_rom_view : forall W mem, rom_view tfibsegs W mem -> consts_view tfibsegs W mem snp_cr.
Proof. intros W mem Hr a Ha. apply Hr. apply snp_cr_in_rom. exact Ha. Qed.
End c.
