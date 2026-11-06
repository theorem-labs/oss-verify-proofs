(* lv2_locate_manifest_readings: the assembly of the segments into readings_spec. The scan's loop closes by induction
   on the fuel f (fm plain readings_scan.v LoopAt) and plain_local's loop by induction on the bytes left. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC20 YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base FMW_rd_cuts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
(* the segments (FMW_rd_pre.v, FMW_rd_lp.v, FMW_rd_pp.v, FMW_rd_c8.v, FMW_rd_pl.v) *)
Hypothesis SEG_E : (forall f, rd_seg_L B CTX f) -> rd_seg_E B CTX.
Hypothesis SEG_L : forall f, rd_seg_L B CTX f -> rd_seg_P B CTX (S f) -> rd_seg_L B CTX (S f).
Hypothesis SEG_P : forall f, rd_seg_L B CTX f -> rd_seg_C8 B CTX (S f) -> rd_seg_P B CTX (S f).
Hypothesis SEG_C8 : forall f, rd_seg_L B CTX f -> (forall m, rd_seg_PL B CTX (S f) m) -> rd_seg_C8 B CTX (S f).
Hypothesis SEG_PL : forall f m, rd_seg_L B CTX f -> rd_seg_PL B CTX (S f) m -> rd_seg_PL B CTX (S f) (S m).

Lemma rd_seg_L0 : rd_seg_L B CTX 0.
Proof. intros cx i d ly3 S3 W3 regs3 mem3 md3 _ (_ & (_ & Hf & _) & _). lia. Qed.

Lemma rd_seg_PL0 : forall f, rd_seg_PL B CTX f 0.
Proof.
intros f cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 Hm _ (_ & _ & _ & _ & _ & _ & _ & _ & Hq & _). lia.
Qed.

Lemma rd_seg_L_all : forall f, rd_seg_L B CTX f.
Proof.
induction f as [|f IH]; [exact rd_seg_L0|].
assert (HPL : forall m, rd_seg_PL B CTX (S f) m).
{ induction m as [|m IHm]; [apply rd_seg_PL0 | exact (SEG_PL f m IH IHm)]. }
exact (SEG_L f IH (SEG_P f IH (SEG_C8 f IH HPL))).
Qed.

Theorem readings_holds_seg : readings_spec tfibsegs B CTX.
Proof.
intros ly S W regs mem md ch t u rp v tb ub live peak cnt fail HPRE HCX HRO H10 H11 H12 Hrp Hpres Htop Hv Hv63
  Ct Cu Kt Ku Hub Htb HG Hlv Hcnt Hev Hlb.
set (cx := mkRDCX ly S W regs mem md ch t u v tb ub live peak cnt fail).
assert (HB : rd_base B CTX cx).
{ subst rp. unfold rd_base, cx, cx_sp, cx_ulen; cbn.
  repeat (split; [assumption|]). exact Hlb. }
pose proof (SEG_E rd_seg_L_all cx HB) as H. cbn in H.
eapply SRr_mono; [exact H|].
intros W' c' _ (ly' & S' & regs' & mem' & md' & res & Hc & HJ & HK & HP & H10' & HPm & HNR & HVr).
exists ly', S', regs', mem', md', res. subst rp. unfold cx_sp in *; cbn in *.
repeat (split; [assumption|]). exact HVr.
Qed.
End c.
