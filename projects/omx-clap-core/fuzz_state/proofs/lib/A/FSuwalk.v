(* Transfer lemmas for a runtime walk stepped over FSupoison.ARU (any U) instead of AR (U = []): the walks of
   __asan_stack_malloc_k (AF0uU.v, AF0sU.v; recipe in ARU-RECIPE.md at the worktree root). The walk's symbolic run is
   on the machine memory mem; the donor invariant AR holds for unpoison U mem (FSupoison.ARU). A byte the walk reads or
   writes is outside U's shadow bytes when it is off the shadow range (image cells, application memory, the stack) or
   when it is a shadow byte of a free side-stack frame (no heap block holds a frame), so there the two memories agree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s YG0q YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YF0v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation ARU := (FSP.ARU segs B).
(* Off the shadow range [SHADOW_OFF, kHighMemBeg): the image, the low and high application memory, the stack. *)
Definition off_shadow (a : Z) : Prop := a < SHADOW_OFF \/ kHighMemBeg <= a.
Lemma ush_off : forall ly S U W mem md a, ARU ly S U W mem md -> off_shadow a -> FSP.in_ush U a = false.
Proof.
intros ly S U W mem md a H Ha. destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (FSP.ush_facts segs B ly S U W mem md a H E) as (_ & L1 & L2). unfold off_shadow in Ha. lia.
Qed.
(* Any memory m read through unpoison U is m there. *)
Lemma unp_off : forall ly S U W mem md (m : word -> option byte) a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 -> off_shadow a ->
FSP.unpoison U m (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros ly S U W mem md m a H Ha Ho. apply FSP.unpoison_out. rewrite (FSP.wz a Ha). exact (ush_off ly S U W mem md a H Ho).
Qed.
Lemma aview_unp_off : forall ly S U W mem md Hd (m : word -> option byte) a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 -> off_shadow a ->
aview segs Hd (FSP.unpoison U m) a = aview segs Hd m a.
Proof. intros ly S U W mem md Hd m a H Ha Ho. apply FSP.aview_at. exact (unp_off ly S U W mem md m a H Ha Ho). Qed.
(* A cell value read from the donor invariant (on unpoison U mem) holds on mem. *)
Lemma val_mem_unp : forall ly S U W mem md Hd a (n : nat) v, ARU ly S U W mem md ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= SHADOW_OFF \/ kHighMemBeg <= a) ->
val_mem segs (mrestrict Hd (FSP.unpoison U mem)) a n v -> val_mem segs (mrestrict Hd mem) a n v.
Proof.
intros ly S U W mem md Hd a n v H A0 A1 A2 V k Hk. rewrite <- (V k Hk). unfold mbyte, mrestrict.
rewrite (unp_off ly S U W mem md mem (a + Z.of_nat k) H ltac:(lia) ltac:(unfold off_shadow; lia)). reflexivity.
Qed.
Lemma apresent_unp_off : forall ly S U W mem md Hd a, ARU ly S U W mem md -> 0 <= a < 2 ^ 64 -> off_shadow a ->
apresent Hd (FSP.unpoison U mem) a -> apresent Hd mem a.
Proof.
intros ly S U W mem md Hd a H Ha Ho [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite <- (unp_off ly S U W mem md mem a H Ha Ho). exact Hb.
Qed.
(* A byte the donor invariant sees (on unpoison U mem) is visible on mem: a byte of U reads 0xf7 there. *)
Lemma aview_some_unp : forall ly S U W mem md a, ARU ly S U W mem md ->
aview segs (w_H W) (FSP.unpoison U mem) a <> None -> aview segs (w_H W) mem a <> None.
Proof.
intros ly S U W mem md a H Hv. rewrite FSP.aview_mod in Hv |- *.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha. set (a' := a mod 2 ^ 64) in *. clearbody a'.
pose proof H as (_ & _ & PO).
destruct (FSP.in_ush U a') eqn:E.
- rewrite (PO a' E). discriminate.
- rewrite FSP.aview_unpoison_out in Hv; [exact Hv|]. rewrite (FSP.wz a' Ha). exact E.
Qed.
Lemma apresent_unp : forall Hd U (m : word -> option byte) a, apresent Hd m a -> apresent Hd (FSP.unpoison U m) a.
Proof.
intros Hd U m a [Hh [b Hb]]. split; [exact Hh|]. unfold FSP.unpoison.
destruct (FSP.in_ush U _); eexists; [reflexivity | exact Hb].
Qed.
Lemma unp_same : forall U (m1 m2 : word -> option byte) w, m1 w = m2 w -> FSP.unpoison U m1 w = FSP.unpoison U m2 w.
Proof. intros U m1 m2 w E. unfold FSP.unpoison. destruct (FSP.in_ush U _); [reflexivity | exact E]. Qed.
(* Regions at absolute addresses below SHADOW_OFF with no write window (the image's rodata cells). *)
Definition ro_low_chk (rs : list YP09.region) : bool :=
forallb (fun r => match YP09.r_base r with
| None => (YP09.r_whi r <=? YP09.r_wlo r) &&
forallb (fun c => (0 <=? YP09.c_off c) && (YP09.c_off c + YP09.c_len c <=? SHADOW_OFF)) (YP09.r_chunks r)
| Some _ => false end) rs.
Lemma region_ok_unp : forall ly S U W mem md Hd E rs, ARU ly S U W mem md -> ro_low_chk rs = true ->
Forall (region_ok segs E (mrestrict Hd (FSP.unpoison U mem))) rs -> Forall (region_ok segs E (mrestrict Hd mem)) rs.
Proof.
intros ly S U W mem md Hd E rs H C F. unfold ro_low_chk in C. rewrite forallb_forall in C.
rewrite Forall_forall in F |- *. intros r Hr. specialize (C r Hr). specialize (F r Hr).
assert (B0 : base_val E (YP09.r_base r) = 0 /\ YP09.r_whi r <= YP09.r_wlo r /\
forall c, In c (YP09.r_chunks r) -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= SHADOW_OFF).
{ revert C. destruct (YP09.r_base r); intros C; [discriminate C|]. apply andb_prop in C as [Cw Cc].
split; [reflexivity|]. split; [apply Z.leb_le; exact Cw|].
intros c Hc. rewrite forallb_forall in Cc. specialize (Cc c Hc). apply andb_prop in Cc as [C1 C2].
split; [apply Z.leb_le; exact C1 | apply Z.leb_le; exact C2]. }
destruct B0 as (B0 & Bw & Bc). destruct F as (B1 & B2 & Wr & Cs).
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; lia|].
rewrite Forall_forall in Cs |- *. intros c Hc i Hi. destruct (Cs c Hc i Hi) as (b & Hb1 & Hb2).
exists b. split; [exact Hb1|]. rewrite <- Hb2. rewrite B0. unfold mbyte, mrestrict.
pose proof (Bc c Hc) as [L1 L2].
rewrite (unp_off ly S U W mem md mem (0 + YP09.c_off c + i) H); [reflexivity | unfold SHADOW_OFF in *; lia | unfold off_shadow; lia].
Qed.
(* The ARU post from AR on unpoison U mem': the side stack adds no block and the run keeps U's shadow bytes. *)
Lemma ARU_intro : forall ly S S' U W mem mem' md md',
ARU ly S U W mem md -> ablocks B ly S' = ablocks B ly S ->
(forall s, FSP.in_ush U s = true -> aview segs (w_H W) mem' s = aview segs (w_H W) mem s) ->
AR segs B ly S' W (FSP.unpoison U mem') md' -> ARU ly S' U W mem' md'.
Proof.
intros ly S S' U W mem mem' md md' (_ & OK & PO) Eb HU HAR'. split; [exact HAR'|]. split.
- unfold FSP.upoison_ok in *. rewrite Eb. exact OK.
- intros s Hs. rewrite (HU s Hs). exact (PO s Hs).
Qed.
Section l.
Hypothesis LAWS : AR_laws segs B.
(* A shadow byte of a free side-stack frame is not user-poisoned: the frame is owned by the runtime, a block's bytes
   are not (AR_blocks_law), and U lies in whole granules of blocks. *)
Lemma ush_free_frame : forall ly S U W mem md cid pos s, ARU ly S U W mem md ->
0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames S) ->
frame_addr ly cid pos mod 8 = 0 -> fs_frame_bytes cid mod 8 = 0 ->
shadow_addr (frame_addr ly cid pos) <= s < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
FSP.in_ush U s = false.
Proof.
intros ly S U W mem md cid pos s H Hc Hp NF F8 B8 Hs.
destruct (FSP.in_ush U s) eqn:E; [|reflexivity]. exfalso.
pose proof H as (HAR & OK & _).
destruct (FSP.ush_granule B ly S U s OK E) as (g & p & n & Hb & G8 & Gs & Gp & Gn).
pose proof (Z.mul_div_le (req_size n) 8 ltac:(lia)) as RD.
destruct (al_blocks _ _ LAWS ly S W (FSP.unpoison U mem) md p n HAR Hb) as (_ & _ & _ & _ & PR & _).
assert (Hg : frame_addr ly cid pos <= g < frame_addr ly cid pos + fs_frame_bytes cid).
{ unfold shadow_addr in Hs, Gs.
apply Z.mod_divide in G8 as [q Hq]; [|lia]. apply Z.mod_divide in F8 as [f Hf]; [|lia]. apply Z.mod_divide in B8 as [b Hb8]; [|lia].
rewrite Hq, Z.div_mul in Gs by lia. rewrite Hf, Hb8, !Z.div_mul in Hs by lia. lia. }
apply (proj2 (PR g ltac:(lia))). exact (own_free_frame B ly S _ cid pos g (proj1 HAR) Hc Hp NF Hg).
Qed.
End l.
End w.
