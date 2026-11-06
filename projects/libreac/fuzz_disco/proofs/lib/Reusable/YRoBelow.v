From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v YCef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YI0w YI0z YI12 YC4a YC8i YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YC8g YCbj YE2k.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma tfib_segs_ro_tab : map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs =
  [(65536, 131072, false); (196608, 458752, false); (655360, 8192, true); (663552, 5619712, true)].
Proof. vm_compute. reflexivity. Qed.
Lemma tfib_in_roP_below : forall a, in_roP tfibsegs 0xa0280 0xa15a8 a -> a < A_ofl_head.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|unfold A_ofl_head; lia].
pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs s Hs) as Hm.
cbv beta in Hm. rewrite tfib_segs_ro_tab, Hw in Hm. cbn [In] in Hm. unfold A_ofl_head.
destruct Hm as [E|[E|[E|[E|[]]]]]; [injection E; intros; lia | injection E; intros; lia | discriminate E | discriminate E].
Qed.
Section d. Context {rc : YM05.RunCeil}.
#[export] Instance tfib_ro_below_ofl :
  ro_below_ofl (SK := tfib_sink_head) (@pa_segs _ lib_both3_0_listing PB_tfib)
    (@pa_relro_lo _ lib_both3_0_listing PB_tfib) (@pa_relro_hi _ lib_both3_0_listing PB_tfib).
Proof. intros a Ha. exact (tfib_in_roP_below a Ha). Qed.
End d.
