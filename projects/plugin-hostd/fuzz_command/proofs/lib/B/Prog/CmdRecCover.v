(* Every granule of fuzz_command.asan-ubsan's image span [0x10000, 0x606000) (pa_img_range) has a shadow byte the
   allocator record pins (the B twin of lib/A/Prog/CmdRecCover.v; one closed check over the record's lists,
   cmd_img_shadow_cover_ok), so the
   shadow words of every image range are readable at every AR state (cmd_cover_hull), and so are a read-only range's
   (cmd_ro_hull_vis); a read-only string argument meets what a runtime entry's aread_ok asks (cmd_ro_rd); a
   read-only range's addressability holds at every AR state once it holds at one (cmd_ro_addr_kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YM05 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0s YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdGlob CmdRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the closed check, stated on the unfolded term so that cmd_img_shb's use of it is syntactic (a conversion between
   a named constant and its unfolding made the kernel evaluate the check lazily, 719 s) *)
Lemma cmd_img_shadow_cover_ok : crf_cover_from 200000 0x10000 0x606000 = true.
Proof. vm_compute. reflexivity. Qed.
(* every byte of the image has a pinned shadow byte *)
Lemma cmd_img_shb : forall x, 0x10000 <= x < 0x606000 -> exists v, cmd_byte (shadow_of_addr SHADOW_OFF x) = Some v.
Proof.
intros x Hx. pose proof (crf_cover_from_ok _ 0x10000 0x606000 eq_refl cmd_img_shadow_cover_ok x Hx) as K.
destruct (cmd_byte (shadow_of_addr SHADOW_OFF x)) as [v|]; [exists v; reflexivity | congruence].
Qed.

(* Every lemma below is closed over exactly `segs B LAWS HB`, the [IMG] ones over `segs B LAWS HB IMG`
   (the Section form of the per-binary facts' statements). *)
Section cover. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HB : CmdBSyms B.
(* the shadow words of every image range are readable at every AR state *)
Lemma cmd_cover_hull : forall ly S (W : world segs) mem md p n,
AR segs B ly S W mem md -> 0x10000 <= p -> p + n <= 0x606000 -> 0 < n -> shadow_hull_vis (aview segs (w_H W) mem) p n.
Proof using LAWS HB.
intros ly S W mem md p n HAR Hp Hn Hn0 s Hs.
pose proof (crf_hull_lo p s Hp (proj1 Hs)) as L1. pose proof (crf_hull_hi (p + n - 1) s ltac:(lia) (proj2 Hs)) as L2.
destruct (cmd_img_shb (8 * (s - SHADOW_OFF)) ltac:(lia)) as [v Hv].
assert (E : shadow_of_addr SHADOW_OFF (8 * (s - SHADOW_OFF)) = s).
{ unfold shadow_of_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
rewrite E in Hv. rewrite (cmd_byte_ok segs B LAWS HB ly S W mem md s v HAR Hv). discriminate.
Qed.
Hypothesis IMG : cmd_img_facts segs B.
(* a read-only string argument (astr_argA's read-only branch): what a runtime entry's aread_ok asks of it, beside
   the presence of its bytes (astr_atR) and its addressability *)
Lemma cmd_ro_rd : forall stk ly S (W : world segs) regs mem md p n,
ecall_pre_stk segs B stk ly S W regs mem md ->
(forall i, 0 <= i < n -> in_roP segs CMD_RLO CMD_RHI (p + i)) ->
(forall i, 0 <= i < n -> in_img segs (p + i)) /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) p n) /\
(0 < n -> 0 < p /\ amem_range p n) /\
(forall a, p <= a < p + n -> ~ ascratch_stk stk regs a /\ ~ aerrno_cell B a).
Proof using LAWS HB IMG.
intros stk ly S W regs mem md p n HP Hro.
pose proof HP as ((HAR & _) & _).
assert (BND : forall i, 0 <= i < n -> 0x10000 <= p + i < 0xa6c68) by (intros i Hi; exact (cif_ro_end _ _ IMG (p + i) (Hro i Hi))).
split; [|split; [|split]].
- intros i Hi. destruct (Hro i Hi) as [(s & Hs & _ & Hr)|Hr]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img _ _ IMG (p + i) Hr)].
- intros Hn. pose proof (BND 0 ltac:(lia)) as B0. pose proof (BND (n - 1) ltac:(lia)) as B1.
  apply (cmd_cover_hull ly S W mem md p n HAR); lia.
- intros Hn. pose proof (BND 0 ltac:(lia)) as B0. pose proof (BND (n - 1) ltac:(lia)) as B1.
  split; [lia | left; unfold kLowMemEnd; lia].
- intros a Ha. pose proof (BND (a - p) ltac:(lia)) as Ba. replace (p + (a - p)) with a in Ba by lia. split.
  + apply (cmd_stk_above segs B stk ly S W regs mem md a HP). unfold kLowMemEnd. lia.
  + unfold aerrno_cell. rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.
(* the shadow words of a read-only range, at every AR state *)
Lemma cmd_ro_hull_vis : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md ->
(forall i, 0 <= i < n -> in_roP segs CMD_RLO CMD_RHI (a + i)) -> 0 < n -> shadow_hull_vis (aview segs (w_H W) mem) a n.
Proof using LAWS HB IMG.
intros ly S W mem md a n HAR Hro Hn.
pose proof (cif_ro_end _ _ IMG (a + 0) (Hro 0 ltac:(lia))) as B0. pose proof (cif_ro_end _ _ IMG (a + (n - 1)) (Hro (n - 1) ltac:(lia))) as B1.
apply (cmd_cover_hull ly S W mem md a n HAR); lia.
Qed.
(* a read-only range's addressability holds at every AR state once it holds at one *)
Lemma cmd_ro_addr_kept : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' a n,
AR segs B ly S W mem md -> AR segs B ly' S' W' mem' md' ->
(forall i, 0 <= i < n -> in_roP segs CMD_RLO CMD_RHI (a + i)) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n -> range_addressable (aview segs (w_H W') mem') SHADOW_OFF a n.
Proof using LAWS HB IMG.
intros ly S W mem md ly' S' W' mem' md' a n HAR HAR' Hro HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok).
pose proof (cif_ro_end _ _ IMG (a + (x - a)) (Hro (x - a) ltac:(lia))) as Bx. replace (a + (x - a)) with x in Bx by lia.
destruct (cmd_img_shb x ltac:(lia)) as [v Hv].
rewrite (cmd_byte_ok segs B LAWS HB ly S W mem md _ v HAR Hv) in Hs. injection Hs as <-.
exists v. split; [exact (cmd_byte_ok segs B LAWS HB ly' S' W' mem' md' _ v HAR' Hv) | exact Hok].
Qed.
End cover.
Print Assumptions cmd_cover_hull.
Print Assumptions cmd_ro_rd.
Print Assumptions cmd_ro_hull_vis.
Print Assumptions cmd_ro_addr_kept.
