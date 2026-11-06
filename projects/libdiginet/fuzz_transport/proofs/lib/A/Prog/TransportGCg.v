(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* TransportGCg: the call kit of the G-form caller-journal walks (lib/A/W_journalG.v ajournal_gx with XO = 0 and
   OUT = []). Every definition and lemma here is stated over a segment list segs, a record B and a range list G, so the
   walks of both images use it; nothing here names a program function or an image value.
   - acall_kept_g: YCbq.v acall_kept whose image clause keeps only the image bytes outside G (a G-form call may
     change the program's own globals); acall_kept_g_of (a donor call's acall_kept is an acall_kept_g at any G).
   - gx_kept / gx_noerrno: every byte of G kept; no byte of G is errno. gx_kept_of_acall_kept: a donor call keeps G.
   - gx_kept_ex: every byte of G outside a written range E kept (refl, trans, of_kept, step): the G part of a G-form
     walk's keep, beside acall_kept_g.
   - dcg_post: the donor-form caller-journal call post (the generic text of a unit's donor cg post, at segs);
     transport_cg_post: the same post in the G form (ajournal_gx G 0 [] and acall_kept_g G).
   - gx_open / gx_pack0 / gx_lift: the donor journal inside a G journal, and back (the same start memory).
   - gx_call_cg: a call to a donor-form callee, lifted into the G form; gx_call_leaf: a call whose post has the
     leaf-bridge form (W unchanged, the caller's donor journal at the return), lifted into the G form.
   - transport_cg_post_out outs: transport_cg_post whose acall_kept_g is read at the memory with the OUT CELLS (a cell
     of the caller's own machine frame the callee writes through a pointer argument) put back as they were at the
     call; transport_cg_post_out_nil (at outs = [] it is transport_cg_post), and the folds a caller's walk does at
     the call: dk_kept_trans_out_g and transport_cg_post_out_fold.
   - gx_rw: every byte of G is a byte of a loaded segment that is readable and writable (gx_rwb, decided by
     gx_rw_of_b), so at EVERY memory a byte of G is writable (gx_rw_writable) and visible (gx_rw_vis): a walk never needs
     the presence of G's bytes, and no call has to keep it.
   - aentry_post / ascratch_ok / aj_gx_entry_at: a runtime entry whose writes are to G or to awr_bytes, called from a
     G journal; gx_intrin_at: __asan_memcpy / __asan_memset (aintrin_realizes) with a destination in G or in awr_bytes.
   - transport_twr_ok_g: the write right a G-form caller gives a callee (each byte a present awr_byte, or a byte of G).
   - the step lemmas that carry acall_kept_g through a walk: dk_kept_refl_g, dk_kept_trans_g, dk_kept_step_g,
     dk_kept_run_g, dk_kept_own_g, dk_kept_trans_nf_g, dk_kept_frame_byte_g, dk_kept_ra_g. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the bytes of G in the image's segments ---- *)
Section rw.
Variable segs : list Segment.

(* a's byte is a byte of a loaded segment that is writable (LPS wview reads it at the empty memory) and readable
   (YP09 mbyte, that is YK11.seg_rom, reads it at the empty memory). *)
Definition gx_rwb (a : Z) : bool :=
  match wview segs (fun _ => None) (Z_to_bv 64 a) with Some _ => true | None => false end &&
  match mbyte segs (fun _ => None) a with Some _ => true | None => false end.
Definition gx_rw (G : list (Z * Z)) : Prop := forall a, inG G a -> gx_rwb a = true.
(* The bytes of G, for the decision of gx_rw by vm_compute. *)
Definition gx_bytes (G : list (Z * Z)) : list Z :=
  flat_map (fun r => map (fun i => fst r + Z.of_nat i) (seq 0 (Z.to_nat (snd r)))) G.

Lemma gx_bytes_in : forall G a, inG G a -> In a (gx_bytes G).
Proof.
intros G a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Har). unfold in_zr in Har.
unfold gx_bytes. apply in_flat_map. exists r. split; [exact Hr|]. apply in_map_iff.
exists (Z.to_nat (a - fst r)). split; [lia | apply in_seq; lia].
Qed.
Lemma gx_rw_of_b : forall G, forallb gx_rwb (gx_bytes G) = true -> gx_rw G.
Proof. intros G H a Ha. rewrite forallb_forall in H. exact (H a (gx_bytes_in G a Ha)). Qed.
Lemma gx_rw_nil : gx_rw [].
Proof. intros a H. exfalso. exact (inG_nil a H). Qed.
Lemma gx_rw_app : forall G1 G2, gx_rw G1 -> gx_rw G2 -> gx_rw (G1 ++ G2).
Proof. intros G1 G2 H1 H2 a Ha. apply inG_app in Ha as [Ha|Ha]; [exact (H1 a Ha) | exact (H2 a Ha)]. Qed.
Lemma gx_rw_sub : forall G1 G2, (forall a, inG G1 a -> inG G2 a) -> gx_rw G2 -> gx_rw G1.
Proof. intros G1 G2 Hs H2 a Ha. exact (H2 a (Hs a Ha)). Qed.

Lemma gx_rw_some : forall {T : Type} (o : option T), match o with Some _ => true | None => false end = true -> o <> None.
Proof. intros T [x|] H; [discriminate | discriminate H]. Qed.
Lemma gx_wview_none : forall (m : word -> option byte) x, m x = None -> wview segs m x = wview segs (fun _ => None) x.
Proof. intros m x H. unfold wview. rewrite H. reflexivity. Qed.
Lemma gx_mbyte_none : forall (m : word -> option byte) a, m (Z_to_bv 64 a) = None -> mbyte segs m a = mbyte segs (fun _ => None) a.
Proof. intros m a H. unfold mbyte. rewrite H. reflexivity. Qed.

(* A byte of G is writable at every memory. *)
Lemma gx_rw_writable : forall G a, gx_rw G -> inG G a -> forall m, writable_at segs m a.
Proof.
intros G a HR Ha m. pose proof (HR a Ha) as E. unfold gx_rwb in E. apply andb_prop in E as [E1 _].
apply gx_rw_some in E1. unfold writable_at. destruct (m (Z_to_bv 64 a)) eqn:Em.
- unfold wview. rewrite Em. discriminate.
- rewrite (gx_wview_none m _ Em). exact E1.
Qed.
(* A byte of G is visible at every memory and every hidden set. *)
Lemma gx_rw_vis : forall G a, gx_rw G -> inG G a -> forall (H : word -> bool) m, aview segs H m a <> None.
Proof.
intros G a HR Ha H m. pose proof (HR a Ha) as E. unfold gx_rwb in E. apply andb_prop in E as [_ E2].
apply gx_rw_some in E2. unfold aview. destruct (mrestrict H m (Z_to_bv 64 a)) eqn:Em.
- unfold mbyte. rewrite Em. cbn. discriminate.
- rewrite (gx_mbyte_none (mrestrict H m) a Em). destruct (mbyte segs (fun _ => None) a) eqn:Eb.
  + cbn. discriminate.
  + exfalso. exact (E2 eq_refl).
Qed.
End rw.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* ---- what a G-form call keeps ---- *)

(* YCbq.v acall_kept, with the image clause guarded by ~ inG G a. *)
Definition acall_kept_g (G : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
 aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall a, in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
 (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
 ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).

Lemma acall_kept_g_of : forall G lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop),
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> acall_kept_g G lyc Sc W memc W2 mem2 slo shi E.
Proof.
intros G lyc Sc W memc W2 mem2 slo shi E (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [exact K2|]. split; [intros a Hi _ Hno He; exact (K3 a Hi Hno He)|].
split; [exact K4|]. split; [exact K5 | exact K6].
Qed.

Lemma acall_kept_g_nil : forall lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop),
  acall_kept_g [] lyc Sc W memc W2 mem2 slo shi E <-> acall_kept segs B lyc Sc W memc W2 mem2 slo shi E.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E. split; [|apply acall_kept_g_of].
intros (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [exact K2|]. split; [intros a Hi Hno He; exact (K3 a Hi (inG_nil a) Hno He)|].
split; [exact K4|]. split; [exact K5 | exact K6].
Qed.

Lemma acall_kept_g_G_mono : forall G G' lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop),
  (forall a, inG G a -> inG G' a) ->
  acall_kept_g G lyc Sc W memc W2 mem2 slo shi E -> acall_kept_g G' lyc Sc W memc W2 mem2 slo shi E.
Proof.
intros G G' lyc Sc W memc W2 mem2 slo shi E Hs (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [exact K2|].
split; [intros a Hi HnG Hno He; exact (K3 a Hi (fun HG => HnG (Hs a HG)) Hno He)|].
split; [exact K4|]. split; [exact K5 | exact K6].
Qed.

Lemma acall_kept_g_weaken : forall G lyc Sc W memc W2 mem2 slo shi (E E' : Z -> Prop),
  (forall a, E a -> E' a) ->
  acall_kept_g G lyc Sc W memc W2 mem2 slo shi E -> acall_kept_g G lyc Sc W memc W2 mem2 slo shi E'.
Proof.
intros G lyc Sc W memc W2 mem2 slo shi E E' HE (K1 & K2 & K3 & K4 & K5 & K6).
split; [exact K1|]. split; [intros b m i Hb Hi Hn; exact (K2 b m i Hb Hi (fun X => Hn (HE _ X)))|].
split; [exact K3|]. split; [intros cid pos a Hin Hr Hn; exact (K4 cid pos a Hin Hr (fun X => Hn (HE _ X)))|].
split; [exact K5 | exact K6].
Qed.

(* Every byte of G kept, and no byte of G is errno. *)
Definition gx_kept (G : list (Z * Z)) (W : world segs) (memc : word -> option byte) (W2 : world segs)
  (mem2 : word -> option byte) : Prop :=
forall a, inG G a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.
Definition gx_noerrno (G : list (Z * Z)) : Prop := forall a, inG G a -> ~ (as_errno B <= a < as_errno B + 4).

(* A donor call changes no byte of G: G is image bytes outside the owned statics (gx_ok) and outside errno. *)
Lemma gx_kept_of_acall_kept : forall G lyc Sc W memc W2 mem2 slo shi (E : Z -> Prop),
  gx_ok segs B G -> gx_noerrno G ->
  acall_kept segs B lyc Sc W memc W2 mem2 slo shi E -> gx_kept G W memc W2 mem2.
Proof.
intros G lyc Sc W memc W2 mem2 slo shi E HG HE (_ & _ & K3 & _) a Ha.
destruct (HG a Ha) as [Hi Hno]. exact (K3 a Hi Hno (HE a Ha)).
Qed.

(* G kept, read range by range (the form TWorldG.v tw_kept_G takes). *)
Lemma gx_kept_rows : forall G W memc W2 mem2, gx_kept G W memc W2 mem2 ->
  forall b n i, In (b, n) G -> 0 <= i < n ->
  aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i).
Proof.
intros G W memc W2 mem2 HK b n i Hin Hi. apply HK. unfold inG. apply Exists_exists.
exists (b, n). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma gx_kept_refl : forall G W memc, gx_kept G W memc W memc.
Proof. intros G W memc a _. reflexivity. Qed.

Lemma gx_kept_trans : forall G W1 mem1 W2 mem2 W3 mem3,
  gx_kept G W1 mem1 W2 mem2 -> gx_kept G W2 mem2 W3 mem3 -> gx_kept G W1 mem1 W3 mem3.
Proof. intros G W1 mem1 W2 mem2 W3 mem3 H12 H23 a Ha. rewrite (H23 a Ha). exact (H12 a Ha). Qed.

(* A call that changes only its stack scratch [lo, hi) (above the low memory) and a set Wr apart from G keeps G (the
   kept clause of a leaf-bridge post or of a runtime contract). *)
Lemma gx_kept_of_win : forall G (W : world segs) memc mem2 lo hi (Wr : Z -> Prop),
  gx_ok segs B G -> kLowMemEnd <= lo ->
  (forall a, inG G a -> ~ Wr a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ Wr a -> aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) ->
  gx_kept G W memc W mem2.
Proof.
intros G W memc mem2 lo hi Wr HG Hlo HWr Hk a Ha.
pose proof (inG_low segs B segs_low G a HG Ha) as Hl. unfold kLowMemEnd in *.
apply Hk; [lia | lia | exact (HWr a Ha)].
Qed.

(* Every byte of G outside a written range E kept: what a G-form walk carries beside acall_kept_g, whose image clause
   leaves G out (the G bytes it reads after its own writes, and the post's promise about G). *)
Definition gx_kept_ex (G : list (Z * Z)) (E : Z -> Prop) (W : world segs) (memc : word -> option byte)
  (W2 : world segs) (mem2 : word -> option byte) : Prop :=
forall a, inG G a -> ~ E a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a.

Lemma gx_kept_ex_refl : forall G E W memc, gx_kept_ex G E W memc W memc.
Proof. intros G E W memc a _ _. reflexivity. Qed.

Lemma gx_kept_ex_trans : forall G E W1 m1 W2 m2 W3 m3,
  gx_kept_ex G E W1 m1 W2 m2 -> gx_kept_ex G E W2 m2 W3 m3 -> gx_kept_ex G E W1 m1 W3 m3.
Proof. intros G E W1 m1 W2 m2 W3 m3 H12 H23 a Ha Hn. rewrite (H23 a Ha Hn). exact (H12 a Ha Hn). Qed.

Lemma gx_kept_ex_of_kept : forall G E W memc W2 mem2, gx_kept G W memc W2 mem2 -> gx_kept_ex G E W memc W2 mem2.
Proof. intros G E W memc W2 mem2 H a Ha _. exact (H a Ha). Qed.

(* One step that changes only the bytes Zs keeps gx_kept_ex when each byte of Zs in G is in E (a byte of G is below
   kLowMemEnd, inG_low). *)
Lemma gx_kept_ex_step : forall G E (W : world segs) memc memX memY (Zs : Z -> Prop),
  gx_ok segs B G -> (forall a, Zs a -> inG G a -> E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  gx_kept_ex G E W memc W memX -> gx_kept_ex G E W memc W memY.
Proof.
intros G E W memc memX memY Zs HG HZ Hk HX a Ha Hn.
pose proof (inG_low segs B segs_low G a HG Ha) as Hl. unfold kLowMemEnd in Hl.
rewrite Hk; [exact (HX a Ha Hn) | lia | intros HZa; exact (Hn (HZ a HZa Ha))].
Qed.

(* ---- the two call posts ---- *)

(* The donor-form caller-journal call post: the caller's donor journal extended by at most EV events, the
   callee-saved registers kept, the side-stack frames of the call state exactly, the caller's blocks exactly, every
   byte outside the call's stack window [spZ regs - FSTK, spZ regs) and outside the written range E kept (acall_kept),
   the meter charged at most COST, and the statement's own facts X. *)
Definition dcg_post (MT : ameter_ops) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (FSTK EV COST : Z) (E : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 e,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
    0 <= e <= EV /\ ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    acall_kept segs B lyc Sc W memc W2 mem2 (spZ regs - FSTK) (spZ regs) E /\
    mo_le MT Sc S2 COST /\
    X regs2 W2 mem2.

(* The same post in the G form: the caller's G journal (XO = 0, no out cell) and acall_kept_g G. *)
Definition transport_cg_post (MT : ameter_ops) (G : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout)
    (S : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (FSTK EV COST : Z) (E : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 e,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
    0 <= e <= EV /\ ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    acall_kept_g G lyc Sc W memc W2 mem2 (spZ regs - FSTK) (spZ regs) E /\
    mo_le MT Sc S2 COST /\
    X regs2 W2 mem2.

Lemma transport_cg_post_X_mono : forall MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST
    (E : Z -> Prop) (X X' : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) W2 c2,
  (forall regs2 W2' mem2, X regs2 W2' mem2 -> X' regs2 W2' mem2) ->
  transport_cg_post MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2 ->
  transport_cg_post MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X' W2 c2.
Proof.
intros MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X X' W2 c2 HX
  (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ & HP & Hfr & Hperm & HK & HMO & HXp).
exists ly2, S2, regs2, mem2, md2, e. repeat (split; [assumption|]). exact (HX _ _ _ HXp).
Qed.

(* ---- out cells: a callee that writes a cell of its CALLER's machine frame ---- *)

(* A callee may write a cell its caller passed it by address in the CALLER's own machine frame (an int * at the
   caller's sp + k; the caller takes no side-stack frame for it). Such a byte is at or above alloc_ceiling and
   OUTSIDE the callee's stack window, where acall_kept_g's first clause keeps every byte whatever the written range
   is, so the callee's post cannot be acall_kept_g at the memory it returns. transport_cg_post_out states it at the
   memory with the out cells put back as they were at the call (W_journalG.v gover outs mem2 memc): every byte
   acall_kept_g keeps is kept but those, and the post's X says what they hold. The caller folds it into its own
   running kept fact with dk_kept_trans_out_g / transport_cg_post_out_fold: the cells lie in the CALLER's own window,
   where its own post keeps nothing. *)

(* acall_kept_g reads a memory only byte by byte. *)
Lemma acall_kept_g_mem_ext : forall G lyc Sc W memc W2 (ma mb : word -> option byte) slo shi (E : Z -> Prop),
  (forall x, mb x = ma x) ->
  acall_kept_g G lyc Sc W memc W2 ma slo shi E -> acall_kept_g G lyc Sc W memc W2 mb slo shi E.
Proof.
intros G lyc Sc W memc W2 ma mb slo shi E Hm (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hv : forall (H : word -> bool) a, aview segs H mb a = aview segs H ma a)
  by (intros H a; apply aview_eq_of; unfold mrestrict; rewrite Hm; reflexivity).
assert (Hp : forall (H : word -> bool) a, apresent H ma a -> apresent H mb a)
  by (intros H a (Hh & b & Hb); split; [exact Hh | exists b; rewrite Hm; exact Hb]).
split; [intros a Ha Hw; rewrite Hv; exact (K1 a Ha Hw)|].
split; [intros b n i Hb Hi Hn; rewrite Hv; exact (K2 b n i Hb Hi Hn)|].
split; [intros a Hi HnG Hno He; rewrite Hv; exact (K3 a Hi HnG Hno He)|].
split; [intros cid pos a Hin Hr Hn; rewrite Hv; exact (K4 cid pos a Hin Hr Hn)|].
split; [intros a Ha Hw Hpr; apply Hp; exact (K5 a Ha Hw Hpr) | intros a Ha; apply Hp; exact (K6 a Ha)].
Qed.

Lemma gover_nil_mem : forall (ma mb : word -> option byte) x, gover [] ma mb x = ma x.
Proof. intros ma mb x. unfold gover, inGb. cbn. reflexivity. Qed.
Lemma gover_out_mem : forall outs (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ inG outs a -> gover outs ma mb (Z_to_bv 64 a) = ma (Z_to_bv 64 a).
Proof.
intros outs ma mb a Ha Hn. unfold gover. rewrite unsigned_lit_small by lia.
destruct (inGb outs a) eqn:Eb; [exfalso; exact (Hn (proj1 (inGb_spec outs a) Eb)) | reflexivity].
Qed.
Lemma gover_out_aview : forall outs (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ inG outs a -> aview segs H (gover outs ma mb) a = aview segs H ma a.
Proof.
intros outs H ma mb a Ha Hn. apply aview_eq_of. unfold mrestrict.
rewrite (gover_out_mem outs ma mb a Ha Hn). reflexivity.
Qed.
Lemma gover_out_apresent : forall outs (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ inG outs a -> apresent H (gover outs ma mb) a -> apresent H ma a.
Proof.
intros outs H ma mb a Ha Hn (Hh & b & Hb). rewrite (gover_out_mem outs ma mb a Ha Hn) in Hb.
split; [exact Hh | exists b; exact Hb].
Qed.
(* A visible byte outside the image is present (the image reads nothing there). *)
Lemma apresent_of_aview : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hi Hv. unfold aview in Hv. unfold mbyte in Hv. unfold apresent.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em.
- unfold mrestrict in Em. destruct (H (Z_to_bv 64 a)) eqn:Hh; [discriminate Em|].
  split; [reflexivity | exists b; exact Em].
- rewrite (seg_rom_none segs a Ha Hi) in Hv. cbn in Hv. exfalso. exact (Hv eq_refl).
Qed.

(* transport_cg_post with acall_kept_g read at the memory whose out cells are the call's (gover outs mem2 memc). *)
Definition transport_cg_post_out (MT : ameter_ops) (G outs : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (W0 : world segs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (FSTK EV COST : Z) (E : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 e,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
    0 <= e <= EV /\ ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    acall_kept_g G lyc Sc W memc W2 (gover outs mem2 memc) (spZ regs - FSTK) (spZ regs) E /\
    mo_le MT Sc S2 COST /\
    X regs2 W2 mem2.

(* With no out cell it is transport_cg_post. *)
Lemma transport_cg_post_out_nil : forall MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST
    (E : Z -> Prop) (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) W2 c2,
  transport_cg_post_out MT G [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2 <->
  transport_cg_post MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2.
Proof.
intros MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E X W2 c2.
split; intros (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ & HP & Hfr & Hperm & HK & HMO & HXp);
  exists ly2, S2, regs2, mem2, md2, e;
  (split; [exact Hc|]); (split; [exact He|]); (split; [exact HJ|]); (split; [exact HP|]); (split; [exact Hfr|]);
  (split; [exact Hperm|]); (split; [| split; [exact HMO | exact HXp]]).
- exact (acall_kept_g_mem_ext G lyc Sc W memc W2 (gover [] mem2 memc) mem2 _ _ E
    (fun x => eq_sym (gover_nil_mem mem2 memc x)) HK).
- exact (acall_kept_g_mem_ext G lyc Sc W memc W2 mem2 (gover [] mem2 memc) _ _ E (gover_nil_mem mem2 memc) HK).
Qed.

(* THE FOLD a caller's walk does at the call. The callee's kept fact is at the memory with the out cells put back and
   at the CALLEE's window; the walk's own running kept fact is at its OWN window, which contains both that window
   (the journal's stack premises) and the out cells (they are bytes of the walk's own frame). The walk's own window
   is where its own post keeps nothing, so the out cells need no exception there: the result is the walk's kept fact
   at the memory the call returned. *)
Lemma dk_kept_trans_out_g : forall G outs lyc Sc (W : world segs) memc mdc (W1 : world segs) memX (W2 : world segs)
    mem2 slo shi slo' shi' (Eo Eo' : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, inG outs a -> slo <= a < shi) ->
  (forall a, inG outs a -> apresent (w_H W2) mem2 a) ->
  acall_kept_g G lyc Sc W memc W1 memX slo shi Eo ->
  acall_kept_g G lyc Sc W1 memX W2 (gover outs mem2 memX) slo' shi' Eo' ->
  slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a) ->
  acall_kept_g G lyc Sc W memc W2 mem2 slo shi Eo.
Proof.
intros G outs lyc Sc W memc mdc W1 memX W2 mem2 slo shi slo' shi' Eo Eo' HAR Hce Hshi Hout Hpres
  (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HnG : forall a, a < alloc_ceiling -> ~ inG outs a) by (intros a Ha Hin; pose proof (Hout a Hin); lia).
assert (Hgv : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
  aview segs (w_H W2) (gover outs mem2 memX) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; exact (gover_out_aview outs (w_H W2) mem2 memX a Ha Hn)).
assert (Hgp : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
  apresent (w_H W2) (gover outs mem2 memX) a -> apresent (w_H W2) mem2 a)
  by (intros a Ha Hn Hp; exact (gover_out_apresent outs (w_H W2) mem2 memX a Ha Hn Hp)).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
  rewrite <- (Hgv a ltac:(lia) Hn). rewrite L1 by lia. apply K1; assumption.
- intros b n i Hb Hi Hn.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hb) as (_ & H4096 & Hbce & _).
  assert (Hno : ~ inG outs (b + i)) by (apply HnG; lia).
  rewrite <- (Hgv (b + i) ltac:(lia) Hno).
  rewrite (L2 b n i Hb Hi) by (intros Y; exact (Hn (HE _ Y))). apply (K2 b n i Hb Hi Hn).
- intros a Hi HnGg Hno He. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  assert (Hn : ~ inG outs a) by (apply HnG; lia).
  rewrite <- (Hgv a ltac:(lia) Hn). rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (Hn2 : ~ inG outs a) by (apply HnG; lia).
  rewrite <- (Hgv a ltac:(lia) Hn2).
  rewrite (L4 cid pos a Hin Hr) by (intros Y; exact (Hn (HE _ Y))). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
  apply (Hgp a ltac:(lia) Hn). apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (inGb outs a) eqn:Eb.
  + exact (Hpres a (proj1 (inGb_spec outs a) Eb)).
  + assert (Hn : ~ inG outs a) by (apply inGb_false; exact Eb).
    apply (Hgp a ltac:(lia) Hn).
    destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
    * apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
    * apply L6. lia.
    * apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.

(* The same fold, from the callee's post: what the caller holds after the call. The out cells' presence in the
   returned memory comes from the post's X (it says what they hold, so they are visible) and from their lying above
   alloc_ceiling, where the image reads nothing. *)
Lemma transport_cg_post_out_fold : forall MT G outs STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc
    (W : world segs) memc mdc (W1 : world segs) memX k regs FSTK EV COST (E Eo : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop) slo shi (W2 : world segs) c2,
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 -> slo <= spZ regs - FSTK -> spZ regs <= shi ->
  (forall a, inG outs a -> slo <= a < shi) ->
  (forall a, E a -> Eo a) ->
  (forall regs2 (W2' : world segs) mem2, X regs2 W2' mem2 ->
     forall a, inG outs a -> aview segs (w_H W2') mem2 a <> None) ->
  acall_kept_g G lyc Sc W memc W1 memX slo shi Eo ->
  transport_cg_post_out MT G outs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W1 memX k regs FSTK EV COST E X W2 c2 ->
  exists ly2 S2 regs2 mem2 md2 e,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
    0 <= e <= EV /\ ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    acall_kept_g G lyc Sc W memc W2 mem2 slo shi Eo /\
    mo_le MT Sc S2 COST /\
    X regs2 W2 mem2.
Proof.
intros MT G outs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc W1 memX k regs FSTK EV COST E Eo X slo shi W2 c2
  HAR Hce Hshi Hlo Hhi Hout HEo HX HKP
  (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ & HP & Hfr & Hperm & HK & HMO & HXp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hpres : forall a, inG outs a -> apresent (w_H W2) mem2 a).
{ intros a Hin. pose proof (Hout a Hin) as Hr. apply (apresent_of_aview (w_H W2) mem2 a ltac:(lia)).
  - intros Him. pose proof (segs_low a Him). unfold kLowMemEnd in *. lia.
  - exact (HX regs2 W2 mem2 HXp a Hin). }
exists ly2, S2, regs2, mem2, md2, e.
split; [exact Hc|]. split; [exact He|]. split; [exact HJ|]. split; [exact HP|]. split; [exact Hfr|].
split; [exact Hperm|]. split; [|split; [exact HMO | exact HXp]].
exact (dk_kept_trans_out_g G outs lyc Sc W memc mdc W1 memX W2 mem2 slo shi (spZ regs - FSTK) (spZ regs) Eo E
  HAR Hce Hshi Hout Hpres HKP HK Hlo Hhi HEo).
Qed.

(* ---- the donor journal inside the G journal ---- *)

(* The donor journal inside a G journal: the same window, the same owned frames, and a start memory that agrees
   with the G journal's outside G. *)
Lemma gx_open : forall G STK sp0 FP ly S (W : world segs) mem md own lyc Sc (Wc : world segs) memc mdc k,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  exists memS, ajournal segs B STK sp0 FP ly S W memS md own lyc Sc Wc memc mdc k /\
               gagree G (w_H W) mem memS /\ 0 <= STK.
Proof.
intros G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (HSTK & _ & (memS & HJ & Hag) & _).
rewrite !Z.add_0_r in HJ. exists memS. split; [exact HJ | split; [exact Hag | exact HSTK]].
Qed.

(* The G journal again, from a donor journal at the same start memory (XO = 0, so the out clause is empty). *)
Lemma gx_pack0 : forall G STK sp0 FP ly S (W : world segs) mem md own ly2 S2 (W2 : world segs) mem2 md2 k2 memS,
  0 <= STK -> ajournal segs B STK sp0 FP ly S W memS md own ly2 S2 W2 mem2 md2 k2 -> gagree G (w_H W) mem memS ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W mem md own ly2 S2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S W mem md own ly2 S2 W2 mem2 md2 k2 memS HSTK HJ Hag.
eapply ajournal_gx_pack; [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag |].
intros a Ha _. lia.
Qed.

(* Any step proved at every donor journal of the G journal's start memories is a step of the G journal. *)
Lemma gx_lift : forall G STK sp0 FP ly S (W0 : world segs) mem md own lyc Sc (W : world segs) memc mdc k (c : config)
    (P : (word -> option byte) -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  (forall memS, ajournal segs B STK sp0 FP ly S W0 memS md own lyc Sc W memc mdc k -> SRr segs W c (P memS)) ->
  (forall memS W2 c2, 0 <= STK -> gagree G (w_H W0) mem memS -> P memS W2 c2 -> Q W2 c2) ->
  SRr segs W c Q.
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k c P Q HJ HC HPQ.
destruct (gx_open G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono; [exact (HC memS HJi)|]. intros W2 c2 _ HP. exact (HPQ memS W2 c2 HSTK Hag HP).
Qed.

(* A call to a callee proved in the donor caller-journal form (its contract takes the caller's donor journal and
   ends in dcg_post), from a G-form walk: the callee's post at the G journal, with every byte of G kept. *)
Lemma gx_call_cg : forall MT G STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (c : config) (regs : bvmap 5 word) (FSTK EV COST : Z) (E : Z -> Prop)
    (X : bvmap 5 word -> world segs -> (word -> option byte) -> Prop),
  gx_ok segs B G -> gx_noerrno G ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (forall memS, ajournal segs B STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k ->
     SRr segs W c (dcg_post MT STK sp0 FP ly S W0 memS md0 own lyc Sc W memc k regs FSTK EV COST E X)) ->
  SRr segs W c (transport_cg_post MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs FSTK EV COST E
    (fun regs2 W2 mem2 => X regs2 W2 mem2 /\ gx_kept G W memc W2 mem2)).
Proof.
intros MT G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k c regs FSTK EV COST E X HG HE HJ HC.
apply (gx_lift G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k c
  (fun memS => dcg_post MT STK sp0 FP ly S W0 memS md0 own lyc Sc W memc k regs FSTK EV COST E X) _ HJ HC).
intros memS W2 c2 HSTK Hag (ly2 & S2 & regs2 & mem2 & md2 & e & Hc & He & HJ2 & HP & Hfr & Hperm & HK & HMO & HX).
exists ly2, S2, regs2, mem2, md2, e.
split; [exact Hc|]. split; [exact He|].
split; [exact (gx_pack0 G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + e) memS HSTK HJ2 Hag)|].
split; [exact HP|]. split; [exact Hfr|]. split; [exact Hperm|].
split; [exact (acall_kept_g_of G lyc Sc W memc W2 mem2 _ _ E HK)|]. split; [exact HMO|].
split; [exact HX | exact (gx_kept_of_acall_kept G lyc Sc W memc W2 mem2 _ _ E HG HE HK)].
Qed.

(* A call whose post has the leaf-bridge form (the world unchanged, the caller's donor journal at the return, at the
   same layout and state, and facts R of the return registers, memory and model): a leaf through the unit's leaf
   bridge (decode_leafb_journal's form), or a runtime contract of that form (YCbq.v aj_intrin_at, aj_bcmp_at), from a
   G-form walk. *)
Lemma gx_call_leaf : forall G STK sp0 FP ly S (W0 : world segs) mem md own lyc Sc (W : world segs) memT mdc k
    (c : config) (raw : word) (R : bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  (forall memS, ajournal segs B STK sp0 FP ly S W0 memS md own lyc Sc W memT mdc k ->
     SRr segs W c (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 memS md own lyc Sc W mem2 md2 k /\ R regs2 mem2 md2)) ->
  SRr segs W c (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ R regs2 mem2 md2).
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k c raw R HJ HC.
apply (gx_lift G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k c _ _ HJ HC).
intros memS W2 c2 HSTK Hag (-> & regs2 & mem2 & md2 & Hc & HJ2 & HR).
split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|].
split; [exact (gx_pack0 G STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k memS HSTK HJ2 Hag) | exact HR].
Qed.

(* ---- runtime entries that write G ---- *)

(* The common post of an entry that keeps the allocator state: W unchanged, back at ra, AR at the same ly S, the
   callee-saved registers kept, the model changed only by materialisation, the result Pr on the new registers and
   memory, every byte outside the written set Wr and the scratch [sp - stk, sp) unchanged, presence kept. *)
Definition aentry_post (stk : Z) ly S (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
Pr regs' mem' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (spZ regs - stk <= a < spZ regs) ->
 aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

(* The pre every entry shares beyond ecall_pre: stk bytes of present scratch below sp, above the stack's floor. *)
Definition ascratch_ok (stk : Z) ly (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
ly_stk_lo ly + stk <= spZ regs /\ (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a).

Lemma aview_wrap64 : forall H (m : word -> option byte) a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
assert (E : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a).
{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. }
rewrite E. reflexivity.
Qed.

(* A runtime entry that keeps the allocator state, given by its contract in aentry_post form, called from a walk
   that holds ajournal_gx G XO OUT, returns with that journal kept (the entry's writes are to G or to awr_bytes of the
   walk's own window outside its out cells), its result Pr, every byte outside its writes and its scratch unchanged,
   and presence kept. The bytes of G it writes need no presence: they are bytes of the image's writable segment
   (gx_rw). *)
Lemma aj_gx_entry_at : forall G XO OUT (stk pc : Z) (Wr : Z -> Prop) (Pr : bvmap 5 word -> (word -> option byte) -> Prop)
  W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
gx_ok segs B G -> XO mod 16 = 0 ->
ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= stk -> stk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
gx_rw segs G ->
(forall a, Wr a -> ~ inG G a ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) ->
(ecall_pre segs B lyc Sc W regsT memT mdc -> ascratch_ok stk lyc W regsT memT ->
 SRr segs W (cfg_at segs pc regsT memT mdc) (aentry_post stk lyc Sc W regsT memT mdc Wr Pr)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ Pr regs2 mem2 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> ~ (sp0 + o - stk <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros G XO OUT stk pc Wr Pr W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
HG HX16 HJ Hsp Hal Hneg Hstk Hbud Hgp Htp Hra Hraw HRW HWa AM.
destruct HJ as (HSTK & HXO & (memS & HJi & Hag) & Hout).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k regsT (o - XO) HJi);
  [lia | rewrite <- Zminus_mod_idemp_r, HX16, Z.sub_0_r; exact Hal | lia | lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
assert (HSC : ascratch_ok stk lyc W regsT memT).
{ split; [rewrite Eslo, Hsp; lia|]. intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
eapply SRr_mono; [exact (AM HPRE HSC)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsame & HPr & Hfr & Hgr).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
(* the memory that is the call's outside G and the caller's on G *)
set (memM := fun x : word => if inGb G (bv_unsigned x) then memT x else mem2 x).
assert (MG : forall x, inGb G (bv_unsigned x) = false -> memM x = mem2 x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (MT : forall x, inGb G (bv_unsigned x) = true -> memM x = memT x) by (intros x Hx; unfold memM; rewrite Hx; reflexivity).
assert (GLO : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (inG_low segs B segs_low G a HG Ha)).
assert (GB : forall a, 0 <= a < 2 ^ 64 -> inGb G (bv_unsigned (Z_to_bv 64 a)) = inGb G a)
by (intros a Ha; rewrite unsigned_lit_small by lia; reflexivity).
assert (AVT : forall a, 0 <= a < 2 ^ 64 -> inG G a -> aview segs (w_H W) memM a = aview segs (w_H W) memT a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MT; [reflexivity|]. rewrite GB by exact Ha. apply inGb_spec. exact HGa. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memM a = aview segs (w_H W) mem2 a).
{ intros a Ha HGa. apply aview_eq_of. unfold mrestrict. rewrite MG; [reflexivity|]. rewrite GB by exact Ha. apply inGb_false. exact HGa. }
assert (HARM : AR segs B lyc Sc W memM md2).
{ eapply (al_frame _ _ LAWS); [exact HAR2 | | | reflexivity | reflexivity | reflexivity |].
  - intros a Ha Ho. apply AV2; [exact Ha|]. intros HGa. destruct (HG a HGa) as [Hi Hno].
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR2 Hi) Ho).
  - intros a Hv. rewrite aview_wrap64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (inGb G a') eqn:Hg.
    + apply inGb_spec in Hg. exact (gx_rw_vis segs G a' HRW Hg (w_H W) memM).
    + rewrite (AV2 a' Ra ltac:(apply inGb_false; exact Hg)). exact Hv.
  - intros a _ Hh. unfold memM. destruct (inGb G (bv_unsigned (w64 a))) eqn:Hg; [|reflexivity].
    exfalso. apply inGb_spec in Hg. pose proof (proj1 (HG _ Hg)) as Hi.
    rewrite (hidden_not_img segs W _ Hi) in Hh. discriminate. }
(* (i) the writes outside G, by the donor's ajournal_after_write *)
assert (HJM : ajournal segs B (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memM md2 k).
{ eapply (ajournal_after_write segs B LAWS segs_low (STK + XO) (sp0 + XO) FP ly S W0 memS md own lyc Sc W memT mdc k memM md2
    (fun a => (Wr a /\ ~ inG G a) \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJi).
  - intros a Ha Hn. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. exact (AVT a Ha Hg).
    + assert (HnG : ~ inG G a) by (apply inGb_false; exact Hg). rewrite (AV2 a Ha HnG).
      apply Hfr; [exact Ha | | intros Hs; apply Hn; right; exact Hs].
      intros HW. apply Hn. left. split; [exact HW | exact HnG].
  - intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memM. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + exact (proj2 (Hgr a (conj Hh (ex_intro _ b Hb)))).
  - exact Hsame.
  - intros a [[HW HnG] | Hs]; left.
    + destruct (HWa a HW HnG) as [[Hs | Hrest] _]; [left; lia | right; exact Hrest].
    + left. lia.
  - exact HARM.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
(* (ii) the writes to G, by W_journalG.v's ajournal_rebase, and (iii) the repack *)
assert (HJ2 : ajournal segs B (STK + XO) (sp0 + XO) FP ly S W0 (gover G memS mem2) md own lyc Sc W mem2 md2 k).
{ apply (ajournal_rebase segs B LAWS segs_low G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 HG HJM).
  - intros x Hx. symmetry. exact (MG x Hx).
  - intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Hh; [exact Hx|].
    destruct (inGb G (bv_unsigned x)) eqn:Hg; [|rewrite (MG x Hg) in Hx; exact Hx].
    rewrite (MT x Hg) in Hx. destruct (memT x) as [b|] eqn:Eb; [|exfalso; exact (Hx eq_refl)].
    assert (Hp : apresent (w_H W) memT (bv_unsigned x)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Eb]).
    destruct (Hgr _ Hp) as [_ [b2 Hb2]]. rewrite Z_to_bv_bv_unsigned in Hb2. rewrite Hb2. discriminate. }
split.
{ apply (ajournal_gx_pack segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k (gover G memS mem2) HSTK HXO HJ2).
  - intros x Hx. unfold mrestrict, gover in *. rewrite Hx. exact (Hag x Hx).
  - intros a Ha Hno. rewrite <- (Hout a Ha Hno). apply Hfr; [lia | | lia].
    intros HW. destruct (inGb G a) eqn:Hg.
    + apply inGb_spec in Hg. pose proof (GLO a Hg). unfold kLowMemEnd in *. lia.
    + destruct (HWa a HW ltac:(apply inGb_false; exact Hg)) as [_ Hn]. exact (Hn Ha). }
split; [exact HP2|]. split; [exact HPr|]. split; [exact Hfr | exact Hgr].
Qed.

(* ---- the write right of a G-form caller ---- *)

(* The caller's right to let a callee write [q, q + n): every byte is one the caller's G journal may change, either
   an awr_byte of the caller's journal that is present, not the runtime's own and not in the ESTACK bytes below sp, or
   a byte of G (writable at every memory by gx_rw, never owned by gx_ok, below every stack). *)
Definition transport_twr_ok_g (G : list (Z * Z)) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world segs) (memc : word -> option byte)
    (sp q n : Z) : Prop :=
  forall a, q <= a < q + n ->
    (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp)) \/
    inG G a.

(* The donor form's write right (each byte an awr_byte) is a G-form write right. *)
Lemma transport_twr_ok_g_of_awr : forall G STK sp0 FP ly S lyc Sc own W memc sp q n,
  (forall a, q <= a < q + n ->
     awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp)) ->
  transport_twr_ok_g G STK sp0 FP ly S lyc Sc own W memc sp q n.
Proof. intros G STK sp0 FP ly S lyc Sc own W memc sp q n H a Ha. left. exact (H a Ha). Qed.

(* From the G journal: an awr_byte is present and not owned (YCbq.v awr_byte_present). *)
Lemma transport_twr_ok_g_intro : forall G STK sp0 FP ly S (W0 : world segs) mem md own lyc Sc (W : world segs) memc mdc k
    sp q n,
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  (forall a, q <= a < q + n ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp - ESTACK <= a < sp)) \/ inG G a) ->
  transport_twr_ok_g G STK sp0 FP ly S lyc Sc own W memc sp q n.
Proof.
intros G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k sp q n HJ H a Ha.
destruct (gx_open G STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k HJ) as (memS & HJi & _ & _).
destruct (H a Ha) as [(Hw & Hs) | HGa]; [left | right; exact HGa].
destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi Hw) as [Hp Ho].
split; [exact Hw | split; [exact Hp | split; [exact Ho | exact Hs]]].
Qed.

(* __asan_memcpy / __asan_memset (aintrin_realizes) from a G-form walk, with a destination the caller's G journal
   may change (transport_twr_ok_g at the call's sp): YCbq.v aj_intrin_at over ajournal_gx G 0 []. A destination
   byte of G is writable by gx_rw, not owned by gx_ok, and below the call's ESTACK window. *)
Lemma gx_intrin_at : forall op pc, aintrin_realizes segs B op pc ->
forall G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
gx_ok segs B G -> gx_rw segs G ->
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
transport_twr_ok_g G STK sp0 FP ly S lyc Sc own W memT (spZ regsT) d n ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros op pc AI G W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
  HG HRW HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ destruct (gx_open G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & _ & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & _) & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
  intros a Ha. destruct (Hdest a Ha) as [(_ & Hp & Ho & Hs) | HGa].
  - split; [apply apresent_writable; exact Hp | split; [exact Ho | exact Hs]].
  - destruct (HG a HGa) as [Hi Hno]. pose proof (inG_low segs B segs_low G a HG HGa) as Hl.
    split; [exact (gx_rw_writable segs G a HRW HGa _)|]. split.
    + intros Ho. apply Hno. exact (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho).
    + unfold kLowMemEnd in *. lia. }
eapply SRr_mono.
{ apply (aj_gx_entry_at G 0 [] ESTACK pc (fun a => d <= a < d + n)
    (fun regs2 mem2 => getr regs2 10 = w64 d /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
          match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end))
    W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HG eq_refl HJ Hsp Hal Hneg (Z.le_refl _) Hbud
    Hgp Htp Hra Hraw HRW).
  - intros a Ha HnG. destruct (Hdest a Ha) as [(Hw & _) | HGa].
    + split; [exact Hw | lia].
    + exfalso. exact (HnG HGa).
  - intros HPRE _. eapply SRr_mono.
    { exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
    hnf. split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HAR2|]. split; [exact HP|]. split; [exact Hsame|].
    split; [split; [exact Hres | exact Heff]|]. split; [exact Hfr | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & (Hres & Heff) & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|].
split; [exact Hfr | exact Hpres2].
Qed.

(* ---- acall_kept_g carried through a walk ---- *)

(* What the call keeps of the caller's memory, carried from the entry memory memc to the current one. *)
Lemma dk_kept_refl_g : forall G lyc Sc W memc slo shi (Eo : Z -> Prop),
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
  acall_kept_g G lyc Sc W memc W memc slo shi Eo.
Proof.
intros G lyc Sc W memc slo shi Eo Hp. unfold acall_kept_g.
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros a _ _ H; exact H|]. intros a Ha; exact (Hp a Ha).
Qed.

Lemma dk_kept_trans_g : forall G lyc Sc W memc W1 memX W2 memY slo shi slo' shi' (Eo Eo' : Z -> Prop),
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  acall_kept_g G lyc Sc W memc W1 memX slo shi Eo ->
  acall_kept_g G lyc Sc W1 memX W2 memY slo' shi' Eo' ->
  slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a) ->
  acall_kept_g G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros G lyc Sc W memc W1 memX W2 memY slo shi slo' shi' Eo Eo' Hce Hshi (K1 & K2 & K3 & K4 & K5 & K6)
  (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i Hb Hi) by (intros X; exact (Hn (HE _ X))). apply (K2 b m i Hb Hi Hn).
- intros a Hi HnG Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn. rewrite (L4 cid pos a Hin Hr) by (intros X; exact (Hn (HE _ X))). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
  + apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
  + apply L6. lia.
  + apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.

(* One step that changes only the bytes Zs keeps acall_kept_g when each of them is in the call's window (above the
   allocation ceiling), in the written range Eo (a block byte or a frame-zone byte), or in G (an image byte). *)
Lemma dk_kept_step_g : forall G lyc Sc W memc mdc memX memY slo shi (Eo Zs : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  acall_kept_g G lyc Sc W memc W memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  (forall a, Zs a -> alloc_ceiling <= a < 2 ^ 64 -> slo <= a < shi) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> Zs (b + i) -> Eo (b + i)) ->
  (forall a, Zs a -> in_img segs a -> ~ inG G a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     Zs a -> Eo a) ->
  acall_kept_g G lyc Sc W memc W memY slo shi Eo.
Proof.
intros G lyc Sc W memc mdc memX memY slo shi Eo Zs HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZw HZb HZi HZf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [apply K1; assumption | lia | intros HZ; exact (Hw (HZw a HZ Ha))].
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hce & _).
  rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia | intros HZ; exact (Hn (HZb b m i Hb Hi HZ))].
- intros a Hi HnG Hno He. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite Hkp; [apply K3; assumption | lia | intros HZ; exact (HZi a HZ Hi HnG Hno He)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | exact Ha | intros HZ; exact (Hn (HZf cid pos a Hin Hr HZ))].
- intros a Ha Hw Hp. apply Hgr. apply K5; assumption.
- intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* The written range Eo lies in the caller's side-stack frames (the frames of the call state Sc). *)
Definition dkg_in_frames (lyc : alayout) (Sc : astate) (Eo : Z -> Prop) : Prop :=
forall a, Eo a -> exists cid pos, In (cid, pos) (frames Sc) /\
frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid.

(* One step of the walk keeps the caller's memory when every byte it may change is in the call's stack window, in
   the written range Eo, in the function's own side-stack frame NF (apart from the caller's), or in G. *)
Lemma dk_kept_run_g : forall G lyc Sc W memc mdc memX memY slo shi (Eo NF Zs : Z -> Prop),
  gx_ok segs B G ->
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  dkg_in_frames lyc Sc Eo ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
  (forall a, NF a -> in_img segs a -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     NF a -> False) ->
  (forall a, NF a -> a < alloc_ceiling) ->
  (forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ NF a \/ inG G a) ->
  acall_kept_g G lyc Sc W memc W memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  acall_kept_g G lyc Sc W memc W memY slo shi Eo.
Proof.
intros G lyc Sc W memc mdc memX memY slo shi Eo NF Zs HG HAR Hce Hshi HEf HNb HNi HNf HNc HZ KP Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (dk_kept_step_g G lyc Sc W memc mdc memX memY slo shi Eo Zs HAR KP Hkp Hgr).
- intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]]; [exact Hw | | pose proof (HNc a Hn); lia |].
  + destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hin0) as (_ & Fce & _). lia.
  + pose proof (inG_low segs B segs_low G a HG Hg). unfold kLowMemEnd in *. lia.
- intros b m i Hb Hi Ha. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  destruct (HZ _ Ha) as [Hw | [Ho | [Hn | Hg]]]; [lia | exact Ho | exfalso; exact (HNb b m i Hb Hi Hn) |].
  exfalso. destruct (HG _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HAR Hb ltac:(lia) Hi').
- intros a Ha Hi HnG _ _. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]]; [lia | | exact (HNi a Hn Hi) | exact (HnG Hg)].
  destruct (HEf a Ho) as (c0 & p0 & Hin0 & Hr0).
  exact (frm_img segs B LAWS lyc Sc W memc mdc c0 p0 a HAR Hin0 Hr0 Hi).
- intros cid pos a Hin Hr Ha. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (G4096 & Gce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  destruct (HZ a Ha) as [Hw | [Ho | [Hn | Hg]]].
  + exfalso. destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
  + exact Ho.
  + exfalso. exact (HNf cid pos a Hin Hr Hn).
  + exfalso. destruct (HG _ Hg) as [Hi _]. pose proof (inG_low segs B segs_low G a HG Hg) as Hl.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos a HAR Hin Hr Hi).
    * pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* A live side-stack frame starts on 64 bytes and has a multiple of 64 bytes, at least 64. *)
Lemma dkg_frame_al64 : forall ly S W mem md cid pos,
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos mod 64 = 0 /\ fs_frame_bytes cid mod 64 = 0 /\ 64 <= fs_frame_bytes cid.
Proof.
intros ly S W mem md cid pos [M _] Hin.
destruct (frame_facts B ly S _ cid pos M Hin) as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & H64 & Hb & _).
unfold frame_addr, page_aligned in *. split; [|split; [exact Hb | exact H64]].
rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
replace (ly_F ly) with (64 * (ly_F ly / 4096 * 64)) by (pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* The bytes of the function's own side-stack frame of class cid (fs_frame_bytes cid bytes at F), its shadow bytes and
   its flag byte FL. *)
Definition dkg_nf (cid F FL a : Z) : Prop :=
(F <= a < F + fs_frame_bytes cid) \/
(SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + fs_frame_bytes cid / 8) \/ a = FL.

Lemma dkg_own_sep : forall ly S W mem md c p Sc c' p',
  AR segs B ly S W mem md -> frames S = (c, p) :: frames Sc -> In (c', p') (frames Sc) ->
  zdisjoint (frame_rng ly (c, p)) (frame_rng ly (c', p')).
Proof.
intros ly S W mem md c p Sc c' p' HAR Hfr Hin.
destruct (in_split _ _ Hin) as (l2 & l3 & E). rewrite E in Hfr.
exact (sep_frames_pos segs B LAWS ly S W mem md (c, p) (c', p') [] l2 l3 HAR Hfr).
Qed.

(* The own frame is apart from everything acall_kept_g keeps: the caller's blocks, the image, the caller's frames and
   their shadow bytes; and it lies below the allocation ceiling. *)
Lemma dkg_nf_sep : forall lyc Sc S2 W mem2 md2 cid fpos F FL,
  AR segs B lyc S2 W mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos ->
  frame_flag_lawP segs B ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> dkg_nf cid F FL (b + i) -> False) /\
  (forall a, dkg_nf cid F FL a -> in_img segs a -> False) /\
  (forall c pos a, In (c, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (c, pos)) \/ in_zr a (shadow_addr (frame_addr lyc c pos), fs_frame_bytes c / 8)) ->
     dkg_nf cid F FL a -> False) /\
  (forall a, dkg_nf cid F FL a -> a < alloc_ceiling).
Proof.
intros lyc Sc S2 W mem2 md2 cid fpos F FL HAR2 Hfrs Eab -> -> FFL. unfold dkg_nf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin : In (cid, fpos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds segs B LAWS _ _ _ _ _ cid fpos HAR2 Hfin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ cid fpos HAR2 Hfin) as (_ & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLce)).
destruct (dkg_frame_al64 _ _ _ _ _ cid fpos HAR2 Hfin) as (HF64 & HFs64 & HFs).
pose proof (fun a Ha => frm_img segs B LAWS _ _ _ _ _ cid fpos a HAR2 Hfin Ha) as HFimg.
set (F := frame_addr lyc cid fpos) in *. set (FL := flag_addr lyc cid fpos) in *.
set (fs := fs_frame_bytes cid) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. pose proof (Z.div_mod fs 64 ltac:(lia)) as DS.
rewrite HF64, Z.add_0_r in DF. rewrite HFs64, Z.add_0_r in DS.
assert (EF : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (ES : fs / 8 = 8 * (fs / 64)) by (rewrite DS at 1; replace (64 * (fs / 64)) with ((8 * (fs / 64)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8 : 0 <= F / 64) by (apply Z.div_pos; lia).
assert (HFS : SHADOW_OFF + F / 8 + fs / 8 <= kHighShadowEnd /\ kLowShadowBeg < SHADOW_OFF + F / 8).
{ unfold SHADOW_OFF, kHighShadowEnd, kLowShadowBeg. lia. }
unfold kHighShadowEnd, kLowShadowBeg, SHADOW_OFF in HFS.
split; [|split; [|split]].
- intros b m i Hb Hi Hn. rewrite <- Eab in Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb) as (_ & Hb4096 & Hbce & Hbapp & Hbown & _).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ b m cid fpos HAR2 Hb Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  destruct Hn as [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia |].
  exact (proj2 (Hbown (b + i) ltac:(lia)) ltac:(rewrite Hn; exact HFLown)).
- intros a Hn Hi. pose proof (segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  destruct Hn as [Hn|[Hn|Hn]]; [exact (HFimg a Hn Hi) | unfold SHADOW_OFF in Hn; lia | subst a; exact (HFLimg Hi)].
- intros c pos a Hin Hr Hn.
  assert (Hin2 : In (c, pos) (frames S2)) by (rewrite Hfrs; right; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ c pos HAR2 Hin2) as (HGal & HGapp & HGpres & HGSpres).
  destruct (dkg_frame_al64 _ _ _ _ _ c pos HAR2 Hin2) as (HG64 & HGs64 & HGs).
  pose proof (dkg_own_sep _ _ _ _ _ cid fpos Sc c pos HAR2 Hfrs Hin) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. fold F fs in Hd.
  set (G := frame_addr lyc c pos) in *. set (gs := fs_frame_bytes c) in *.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
  destruct Hn as [Hn|[Hn|Hn]].
  + destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end G gs ltac:(lia)) as Hse. unfold shadow_addr in Hse, Hr. fold G in Hr.
    assert ((G + gs) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). assert (0 <= G / 8) by (apply Z.div_pos; lia).
    change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF in Hr, Hse. lia.
  + destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [unfold SHADOW_OFF in Hn; lia|].
    unfold shadow_addr in Hr. fold G in Hr.
    pose proof (Z.div_mod G 64 ltac:(lia)) as DG. pose proof (Z.div_mod gs 64 ltac:(lia)) as DGS.
    rewrite HG64, Z.add_0_r in DG. rewrite HGs64, Z.add_0_r in DGS.
    assert (EG : G / 8 = 8 * (G / 64)) by (rewrite DG at 1; replace (64 * (G / 64)) with ((8 * (G / 64)) * 8) by lia; apply Z.div_mul; lia).
    assert (EGS : gs / 8 = 8 * (gs / 64)) by (rewrite DGS at 1; replace (64 * (gs / 64)) with ((8 * (gs / 64)) * 8) by lia; apply Z.div_mul; lia).
    unfold SHADOW_OFF in Hn, Hr. lia.
  + subst a. destruct Hr as [Hr|Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    * exact (proj2 (HGpres FL ltac:(fold G gs; lia)) HFLown).
    * unfold shadow_addr in Hr. fold G in Hr.
      exact (proj2 (HGSpres (FL - shadow_addr G) ltac:(unfold shadow_addr; fold G; lia))
        ltac:(replace (shadow_addr G + (FL - shadow_addr G)) with FL by lia; exact HFLown)).
- intros a [Hn|[Hn|Hn]]; [lia | unfold SHADOW_OFF in Hn; lia | lia].
Qed.

(* One step of the walk keeps the caller's memory when each byte it may change is in the call's stack window, in the
   written range Eo, in the own frame of class cid, or in G. *)
Lemma dk_kept_own_g : forall G lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi cid fpos F FL (Eo Zs : Z -> Prop),
  gx_ok segs B G ->
  AR segs B lyc Sc W memc mdc -> AR segs B lyc S2 W mem2 md2 ->
  frames S2 = (cid, fpos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  F = frame_addr lyc cid fpos -> FL = flag_addr lyc cid fpos -> frame_flag_lawP segs B ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  dkg_in_frames lyc Sc Eo ->
  (forall a, Zs a -> (slo <= a < shi) \/ Eo a \/ dkg_nf cid F FL a \/ inG G a) ->
  acall_kept_g G lyc Sc W memc W memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  acall_kept_g G lyc Sc W memc W memY slo shi Eo.
Proof.
intros G lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi cid fpos F FL Eo Zs HG HAR HAR2 Hfrs Eab EF EFL FFL Hce Hshi
  HEf HZ KP Hkp Hgr.
destruct (dkg_nf_sep lyc Sc S2 W mem2 md2 cid fpos F FL HAR2 Hfrs Eab EF EFL FFL) as (N1 & N2 & N3 & N4).
exact (dk_kept_run_g G lyc Sc W memc mdc memX memY slo shi Eo (dkg_nf cid F FL) Zs HG HAR Hce Hshi HEf N1 N2 N3 N4
  HZ KP Hkp Hgr).
Qed.

(* A callee called while the walk owns a side-stack frame: its acall_kept_g is stated at its call state (ly2, S2),
   whose frames and blocks contain the caller's (Sc), and its written range Eo' lies in the walk's Eo or in the own
   frame NF (given by its separation facts, as dkg_nf_sep gives them). *)
Lemma dk_kept_trans_nf_g : forall G lyc Sc ly2 S2 W memc W1 memX W2 memY slo shi slo' shi' (Eo Eo' NF : Z -> Prop),
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> NF (b + i) -> False) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     NF a -> False) ->
  acall_kept_g G lyc Sc W memc W1 memX slo shi Eo ->
  acall_kept_g G ly2 S2 W1 memX W2 memY slo' shi' Eo' ->
  slo <= slo' -> shi' <= shi -> (forall a, Eo' a -> Eo a \/ NF a) ->
  acall_kept_g G lyc Sc W memc W2 memY slo shi Eo.
Proof.
intros G lyc Sc ly2 S2 W memc W1 memX W2 memY slo shi slo' shi' Eo Eo' NF Hce Hshi Hfa Hfr Hbl HNb HNf
  (K1 & K2 & K3 & K4 & K5 & K6) (L1 & L2 & L3 & L4 & L5 & L6) Hlo Hhi HE.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite L1 by lia. apply K1; assumption.
- intros b m i Hb Hi Hn. rewrite (L2 b m i (Hbl _ Hb) Hi)
    by (intros X; destruct (HE _ X) as [Y|Y]; [exact (Hn Y) | exact (HNb b m i Hb Hi Y)]).
  apply (K2 b m i Hb Hi Hn).
- intros a Hi HnG Hno He. rewrite L3 by assumption. apply K3; assumption.
- intros cid pos a Hin Hr Hn.
  assert (Hr2 : in_zr a (frame_rng ly2 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Hfa; exact Hr).
  rewrite (L4 cid pos a (Hfr _ Hin) Hr2)
    by (intros X; destruct (HE _ X) as [Y|Y]; [exact (Hn Y) | exact (HNf cid pos a Hin Hr Y)]).
  apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. apply L5; [lia | intros [? ?]; apply Hw; lia |]. apply K5; assumption.
- intros a Ha. destruct (Z_lt_ge_dec a slo') as [H1|H1]; [|destruct (Z_lt_ge_dec a shi') as [H2|H2]].
  + apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
  + apply L6. lia.
  + apply L5; [lia | intros [? ?]; lia |]. apply K6. lia.
Qed.

(* The caller's frame bytes outside the written range are those at entry. *)
Lemma dk_kept_frame_byte_g : forall G lyc Sc W memc memX slo shi (Eo : Z -> Prop) cid pos a,
  acall_kept_g G lyc Sc W memc W memX slo shi Eo -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ Eo a ->
  aview segs (w_H W) memX a = aview segs (w_H W) memc a.
Proof.
intros G lyc Sc W memc memX slo shi Eo cid pos a (_ & _ & _ & K4 & _) Hin Ha Hn.
apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hn].
Qed.

(* The shadow of a range of a caller's frame stays addressable when the written range misses its shadow bytes. *)
Lemma dk_kept_ra_g : forall G lyc Sc W memc mdc memX slo shi (Eo : Z -> Prop) cid pos a n,
  AR segs B lyc Sc W memc mdc ->
  acall_kept_g G lyc Sc W memc W memX slo shi Eo -> In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= a -> a + n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall x, a <= x < a + n -> ~ Eo (shadow_addr x)) ->
  range_addressable (aview segs (w_H W) memc) SHADOW_OFF a n ->
  range_addressable (aview segs (w_H W) memX) SHADOW_OFF a n.
Proof.
intros G lyc Sc W memc mdc memX slo shi Eo cid pos a n HAR (_ & _ & _ & K4 & _) Hin Hlo Hhi Hn HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
destruct (al_frames _ _ LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _ & _ & _).
destruct (dkg_frame_al64 lyc Sc W memc mdc cid pos HAR Hin) as (_ & Hfs64 & Hfs).
set (F := frame_addr lyc cid pos) in *.
assert (HR : in_zr (shadow_of_addr SHADOW_OFF x) (shadow_addr F, fs_frame_bytes cid / 8)).
{ unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd].
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as DS.
  assert (HF8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D32. rewrite Hal, Z.add_0_r in D32. rewrite D32.
    replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
  assert (HS8 : fs_frame_bytes cid mod 8 = 0).
  { pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64. rewrite Hfs64, Z.add_0_r in D64. rewrite D64.
    replace (64 * (fs_frame_bytes cid / 64)) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia. apply Z_mod_mult. }
  split.
  - assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia). lia.
  - assert (x / 8 < F / 8 + fs_frame_bytes cid / 8) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite <- Hs. apply (K4 cid pos _ Hin (or_intror HR)). unfold shadow_of_addr.
change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hn. exact Hx.
Qed.

End b.
End a.
