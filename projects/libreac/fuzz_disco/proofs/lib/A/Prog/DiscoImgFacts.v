From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YG00 YG0f YG0n YG0d YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0m AD2l AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable DiscoList DiscoPa DiscoImg DiscoBase DiscoRoClose DiscoEntryInv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma disco_segs_ro_tab : map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) disco_segs =
  [(0x10000, 0x20000, false); (0x30000, 0x6f000, false); (0x9f000, 0x3000, true); (0xa2000, 0x55c000, true)].
Proof. vm_compute. reflexivity. Qed.

Lemma disco_in_roP_below : forall a, in_roP disco_segs disco_relro_lo disco_relro_hi a -> a < AE2k.A_ofl_head.
Proof.
intros a [(s & Hs & Hw & Hr) | Hr]; [|unfold disco_relro_lo, disco_relro_hi in Hr; unfold AE2k.A_ofl_head; lia].
pose proof (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) disco_segs s Hs) as Hm.
cbv beta in Hm. rewrite disco_segs_ro_tab, Hw in Hm. cbn [In] in Hm. unfold AE2k.A_ofl_head.
destruct Hm as [E|[E|[E|[E|[]]]]]; [injection E; intros; lia | injection E; intros; lia | discriminate E | discriminate E].
Qed.

Section d. Context {rc : YM05.RunCeil}.

#[export] Instance disco_ro_below_ofl :
  ro_below_ofl (SK := AE2k.tfib_sink_head) (@pa_segs _ disco_listing PB_disco)
    (@pa_relro_lo _ disco_listing PB_disco) (@pa_relro_hi _ disco_listing PB_disco).
Proof. intros a Ha. exact (disco_in_roP_below a Ha). Qed.

Lemma disco_dglob_cells_b :
  forallb (fun c => existsb (is_shv (fst c) (snd c)) Tfib_const_shadow) (dglob_cells (PI := PB_disco)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma disco_dglob_const : dglob_const (PI := PB_disco) TfibB.
Proof.
intros ly c Hc. pose proof (proj1 (forallb_forall _ _) disco_dglob_cells_b c Hc) as Hb. cbv beta in Hb.
apply existsb_exists in Hb as (x & Hx & Hv). apply is_shv_eq in Hv. subst x.
cbn [as_const TfibB]. unfold Tfib_const. apply in_or_app. right. apply in_or_app. right. exact Hx.
Qed.

Lemma disco_dglob_ranges_b :
  forallb (fun r => existsb (fun z => (fst z <=? fst r) && (fst r + snd r <=? fst z + snd z))%bool Tfib_zero_shadow)
    (dglob_ranges (PI := PB_disco)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma disco_dglob_zshadow : dglob_zshadow (PI := PB_disco) TfibB.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) disco_dglob_ranges_b r Hr) as Hb. cbv beta in Hb.
apply existsb_exists in Hb as (z & Hz & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists z. split; [exact Hz | split; assumption].
Qed.

End d.
