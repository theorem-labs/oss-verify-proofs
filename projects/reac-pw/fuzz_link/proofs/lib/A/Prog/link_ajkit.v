(* reac-pw/fuzz_link, image A: the journal steps the walks of link's own functions take at a call of the runtime's checked
   copy / checked fill (checked_memcpy, checked_memset) and of the string wrappers (wrapper_strnlen, wrapper_strlen,
   wrapper_strncmp), on the caller's program-global journal `ajournal_gx G XO OUT` of lib/A/W_journalG.v (link-a/form/FORM.md
   (internal record, sha256 13aeff774164) sections 0 and 3a: every own-function contract states the caller's journal).

   The kit already lifts these calls onto the donor journal `ajournal` (Reusable/YCbq.v:347-369): YC85G.v:243
   aj_intrin_atS (checked copy / fill), and pcap's aj_strcmp_at (libreac/fuzz_pcap lib/A/Prog/PcapFuzzFopen.v:109).
   Neither applies at a call whose destination lies in G, because the donor journal keeps every image byte outside
   the runtime's statics and errno (YCbq.v:359-360), so aj_intrin_atS asks each destination byte to be an `awr_byte`
   (YC85G.v:249). Link's own code makes such calls: fuzz_send +0xcc (0x8235c) copies the request into g_nl's ring
   (a0 = g_nl + 0x40224 + 512 * i), kernel +0x1ee4 (0x85c14) copies into g_nl (a0 = g_nl + 4096 * i, g_nl's address
   from the frame word +0x38), kernel +0xaf8 (0x84828) fills msg_build.long_alias with 0x61 for 0x12c bytes, and
   LLVMFuzzerTestOneInput +0x304 (0x82ad8) fills g_nl (a0 = 0x5dcac0, a2 = 0x42678 = 271992) with 0.

   Section b (generic: it names only the kit's own names, no address of link):
   - ajournal_gx_after_write: W_journalG.v's ajournal_gx_exec for a step whose effect is given by a runtime
     contract (views kept outside the write set, presence kept, AR at the end) instead of by the program runner.
     Each written byte is an awr_byte of the journal's own window, a byte of G, or an out cell: the per-byte
     condition of ajournal_gx_exec (W_journalG.v:303-304), which is link_amem.v's `ajw` unfolded. Proof: the G
     bytes are moved into the start memory by W_journalG.v's ajournal_rebase, the other bytes go through the donor's
     ajournal_after_write (YCbq.v:514), at the AR the contract gives.
   - aj_gx_ecall_pre: the runtime-call pre-state (YG0d.v:285 ecall_pre, and a scratch window of w bytes below the
     call's sp; for w = 2 * ESTACK the premise of the strnlen / bcmp contracts, for w = stk the RtDefs.v
     ecall_pre_stk) at a call whose window lies inside the journal's window.
   - aj_gx_call_at: the step through any runtime entry whose post has the standard shape (return to ra, AR at the
     call's allocator state, views kept outside its scratch window and its cells Eb, presence kept): the journal at
     the return, and the post's own facts P.
   - aj_gx_call_atF: aj_gx_call_at for an entry whose post returns at another FP state fx' (the printf family:
     snprintf, vfprintf, fprintf, whose posts change the f registers but f10 and leave rounding mode 0; boxreg's
     asnprintf_realizes, lib/A/Rt/SnprintfDef.v, has that shape); P sees fx'.
   - ajournal_gx_after_write_off, aj_gx_call_atFo: the same two with presence asked only for bytes at or above
     alloc_ceiling, plus the visibility of each written byte. A post whose written bytes lie in the image (.bss is
     modelled as ROM zero bytes: seg_rom at g_names is Some 0) pins them only through the view, so it cannot say
     that a written NUL is present in memory; the journal needs presence only on its window, above alloc_ceiling
     (YCbq.v ajournal_after_write uses it there alone; W_journalG.v ajournal_rebase needs only that views stay
     visible). Proof: the step lands on a memory with the same views that is present wherever the call's memory
     was (absent bytes filled from the ROM, or from the call's memory where the ROM has none: there the views
     agree by visibility), and ajournal_gx_end_ext moves the journal to the true memory.
   - aj_gx_intrin_at: the ajournal_gx counterpart of aj_intrin_atS (YC85G.v:243-295) over the same runtime rule
     aintrin_realizes (YG0d.v:325-343), with a destination byte allowed in G (writable) or an out cell. The call's
     window is stated from its sp (`spZ regsT`), as link_amem.v's apre states the callee window, so that a journal
     with XO not a multiple of 16 is covered too.
   - aj_gx_art_at: the ajournal_gx counterpart of plugin-hostd/fuzz_command's aj_art_at (lib/A/Prog/PaArt.v, over
     the RtDefs.v post art_post), with the entry's cells Eb allowed in G.
   Section w (generic, over the string contracts' statements):
   - aj_gx_strnlen_at over lib/Rt/StrnlenDef.v astrnlen_whole_realizesM (window 2 * ESTACK);
   - aj_gx_strlen_at over lib/A/Rt/RtString.v astrlen_realizes (window ESTACK);
   - aj_gx_strncmp_at over lib/A/Rt/RtString.v astrncmp_realizes (window 2 * ESTACK).
   Section la (link's instances): the G objects with a checked write into them are bytes of link_aaddr.v's LA_G, and
   every byte of them is writable at image A's segments (writable_at_of_wseg below and a vm_compute of YK1d.v's
   wseg_ok at tfibsegs, as A/AE36.v does for its cells). The journal does not give that: gx_ok says only that a byte
   of G is an image byte outside the runtime's statics, which a read-only image byte also is.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module LStrFun := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Spec.StrFun.

(* A byte of a range of G is a byte of G. *)
Lemma inG_of_In : forall G b n a, In (b, n) G -> b <= a < b + n -> inG G a.
Proof.
intros G b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.

(* Every byte of [a0, a0 + n) is writable at any memory, when the segments say so for the whole range (YK1d.v
   wseg_ok: each byte lies in a writable segment that has a byte for it). *)
Lemma writable_at_of_wseg : forall segs (m : word -> option byte) a0 n,
  0 <= a0 -> a0 + n <= 2 ^ 64 -> wseg_ok segs (Z_to_bv 64 a0) (Z.to_nat n) = true ->
  forall a, a0 <= a < a0 + n -> writable_at segs m a.
Proof.
intros segs m a0 n Ha0 Hn Hw a Ha. unfold writable_at.
assert (Hu : bv_unsigned (Z_to_bv 64 a0) = a0) by (apply unsigned_lit_small; lia).
apply (store_ok_all segs m (Z.to_nat n) (Z_to_bv 64 a0)).
- rewrite Hu, Z2Nat.id by lia. lia.
- apply store_ok_wseg. exact Hw.
- rewrite Hu, Z2Nat.id by lia. rewrite unsigned_lit_small by lia. lia.
Qed.

(* A view is read at the address modulo 2 ^ 64. *)
Lemma aview_wrap : forall segs H (m : word -> option byte) a,
  aview segs H m a = aview segs H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros segs H m a. unfold aview, mbyte. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head is an explicit argument, as on every pcap statement and in link_amem.v (the only global sink_head
   instance of this closure is the plain build's, Reusable/YI5b.v, so it must never be inferred). *)
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The donor's ajournal_after_write over ajournal_gx: a step that leaves the allocator state, the layout and the
   world as they are, writes the bytes Wr and nothing else (as the walk sees memory), keeps every present byte
   present, and ends at an AR state. *)
Lemma ajournal_gx_after_write : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc'
    (Wr : Z -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  AR segs B lyc Sc Wc memc' mdc' ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HG HJX Heqw Hgr Hsame HW HAR'.
destruct HJX as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _ & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HGlow : forall a, inG G a -> 0 <= a < kLowMemEnd) by (intros a Ha; exact (segs_low a (proj1 (HG a Ha)))).
(* the memory with the step's G bytes and the call-time bytes elsewhere *)
set (memG := fun x : word => if inGb G (bv_unsigned x) then memc' x else memc x).
assert (EG : forall x, inGb G (bv_unsigned x) = true -> memG x = memc' x)
  by (intros x Hx; unfold memG; rewrite Hx; reflexivity).
assert (EN : forall x, inGb G (bv_unsigned x) = false -> memG x = memc x)
  by (intros x Hx; unfold memG; rewrite Hx; reflexivity).
(* 1. the G bytes: the start memory is rebased onto them *)
assert (Hgr1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memG)).
{ intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H Wc x) eqn:Eh; [exact Hx|].
  destruct (inGb G (bv_unsigned x)) eqn:Eg; [rewrite (EG x Eg) | rewrite (EN x Eg); exact Hx].
  destruct (memc x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Hp : apresent (w_H Wc) memc (bv_unsigned x)).
  { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists b; exact Em]. }
  destruct (Hgr _ Hp) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. congruence. }
pose proof (ajournal_rebase segs B LAWS segs_low G (STK + XO) (sp0 + XO) FP ly S W memS md own lyc Sc Wc memc mdc k
  memG HG HJ EN Hgr1) as HJ1.
(* 2. the other bytes: the donor's step, at the AR the contract gives *)
assert (HJ2 : ajournal segs B (STK + XO) (sp0 + XO) FP ly S W (gover G memS memG) md own lyc Sc Wc memc' mdc' k).
{ eapply (ajournal_after_write segs B LAWS segs_low (STK + XO) (sp0 + XO) FP ly S W (gover G memS memG) md own
    lyc Sc Wc memG mdc k memc' mdc' (fun a => Wr a /\ ~ inG G a) Sc own HJ1).
  - intros a Ha Hna. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Eg.
    + apply aview_eq_of. unfold mrestrict. rewrite (EG _ Eg). reflexivity.
    + assert (HnG : ~ inG G a).
      { intros HGa. rewrite unsigned_lit_small in Eg by lia. apply inGb_false in Eg. exact (Eg HGa). }
      rewrite (Heqw a Ha (fun HWa => Hna (conj HWa HnG))).
      symmetry. apply aview_eq_of. unfold mrestrict. rewrite (EN _ Eg). reflexivity.
  - intros a Hp. destruct (inGb G (bv_unsigned (Z_to_bv 64 a))) eqn:Eg.
    + destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EG _ Eg). exact Hb.
    + apply Hgr. destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite <- (EN _ Eg). exact Hb.
  - exact Hsame.
  - intros a [HWa HnG]. left. destruct (HW a HWa) as [[Haw _] | [HGa | [_ Hwin]]].
    + destruct Haw as [Hs | Hrest]; [left; lia | right; exact Hrest].
    + exfalso. exact (HnG HGa).
    + left. lia.
  - exact HAR'.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
(* 3. the gx journal again, at the rebased start memory *)
eapply ajournal_gx_pack; [exact HSTK | exact HXO | exact HJ2 | |].
- intros x Hg. unfold mrestrict, gover. rewrite Hg. exact (Hag x Hg).
- intros a Ha Hno.
  assert (HnW : ~ Wr a).
  { intros HWa. destruct (HW a HWa) as [[_ Hn] | [HGa | [Ho _]]].
    + exact (Hn Ha).
    + pose proof (HGlow a HGa). lia.
    + exact (Hno Ho). }
  rewrite (Heqw a ltac:(lia) HnW). exact (Hout a Ha Hno).
Qed.

(* The journal at an end memory m1 holds at any end memory m2 with the same views, AR and its window present. *)
Lemma ajournal_end_ext : forall STK sp0 FP ly S W mem md own ly' S' W' m1 m2 md' k,
  ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' m1 md' k ->
  AR segs B ly' S' W' m2 md' ->
  (forall a, aview segs (w_H W') m2 a = aview segs (w_H W') m1 a) ->
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') m2 a) ->
  ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' m2 md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' m1 m2 md' k HJ HAR2 Hv Hp.
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR2|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a Ha Hs; rewrite Hv; exact (F1 a Ha Hs)|].
split; [intros p n i H1 H2 Hi Hnf; rewrite Hv; exact (F2 p n i H1 H2 Hi Hnf)|].
split; [intros a Hi Hno He Hsp; rewrite Hv; exact (F3 a Hi Hno He Hsp)|].
split; [intros cid pos a Hin Hr Hnf; rewrite Hv; exact (F4 cid pos a Hin Hr Hnf)|].
split; [exact Hgone|]. split; [exact Hp|]. split; [exact Hstatic|].
split; [intros a Hx He; rewrite Hv; exact (F5 a Hx He) | exact HQT].
Qed.
Lemma ajournal_gx_end_ext : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' m1 m2 md' k,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' m1 md' k ->
  AR segs B ly' S' W' m2 md' ->
  (forall a, aview segs (w_H W') m2 a = aview segs (w_H W') m1 a) ->
  (forall a, sp0 - STK <= a < sp0 + XO -> apresent (w_H W') m2 a) ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' m2 md' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' m1 m2 md' k (HSTK & HXO & (memS & HJ & Hag) & Hout) HAR2 Hv Hp.
apply ajournal_gx_pack with (memS := memS); [exact HSTK | exact HXO | | exact Hag |].
- apply (ajournal_end_ext (STK + XO) (sp0 + XO) FP ly S W memS md own ly' S' W' m1 m2 md' k HJ HAR2 Hv).
  intros a Ha. apply Hp. lia.
- intros a Ha Hno. rewrite Hv. exact (Hout a Ha Hno).
Qed.

(* ajournal_gx_after_write with presence asked only at or above alloc_ceiling, and visibility kept everywhere. *)
Lemma ajournal_gx_after_write_off : forall G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc'
    (Wr : Z -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H Wc) memc' a = aview segs (w_H Wc) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H Wc) memc a <> None -> aview segs (w_H Wc) memc' a <> None) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  AR segs B lyc Sc Wc memc' mdc' ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr HG HJX Heqw Hvis Hoff Hsame HW HAR'.
pose proof HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (E47 : 2 ^ 47 < 2 ^ 64) by (unfold Z.lt; reflexivity).
assert (Hvis' : forall a, aview segs (w_H Wc) memc a <> None -> aview segs (w_H Wc) memc' a <> None).
{ intros a Hv. rewrite (aview_wrap segs _ memc a) in Hv. rewrite (aview_wrap segs _ memc' a).
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 a)) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
  exact (Hvis _ R Hv). }
(* the memory with the step's views that is present wherever memc was *)
set (memP := fun x : word => if w_H Wc x then memc' x else
  match memc' x with
  | Some b => Some b
  | None => match seg_rom segs x with Some r => Some r | None => memc x end
  end).
assert (V : forall a, aview segs (w_H Wc) memP a = aview segs (w_H Wc) memc' a).
{ intros a. pose proof (Hvis' a) as Hva. revert Hva. unfold aview, mbyte, mrestrict, memP. cbv beta.
  destruct (w_H Wc (Z_to_bv 64 a)); [intros _; reflexivity|].
  destruct (memc' (Z_to_bv 64 a)) as [b'|]; [intros _; reflexivity|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [r|]; [intros _; reflexivity|].
  destruct (memc (Z_to_bv 64 a)) as [b|]; [|intros _; reflexivity].
  intros Hva. exfalso. apply Hva; [cbn; intros Hc; discriminate Hc | reflexivity]. }
assert (P : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memP a).
{ intros a [Hh [b Hb]]. split; [exact Hh|]. unfold memP. cbv beta. rewrite Hh.
  destruct (memc' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
  destruct (seg_rom segs (Z_to_bv 64 a)) as [r|]; [exists r; reflexivity | exists b; exact Hb]. }
assert (HARP : AR segs B lyc Sc Wc memP mdc').
{ eapply (al_frame _ _ LAWS); [exact HAR' | | | reflexivity | reflexivity | reflexivity |].
  - intros a _ _. exact (V a).
  - intros a Hv. rewrite V. exact Hv.
  - intros a _ Hh. unfold memP. cbv beta. rewrite Hh. reflexivity. }
pose proof (ajournal_gx_after_write G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memP mdc' Wr HG HJX
  ltac:(intros a Ha Hn; rewrite V; exact (Heqw a Ha Hn)) P Hsame HW HARP) as HJP.
apply (ajournal_gx_end_ext G XO OUT STK sp0 FP ly S W mem md own lyc Sc Wc memP memc' mdc' k HJP HAR').
- intros a. symmetry. exact (V a).
- intros a Ha. apply Hoff; [lia | apply Hpres; lia].
Qed.

(* The pre-state of a runtime call whose scratch window [spZ regsc - w, spZ regsc) lies inside the journal's window:
   YG0d.v's ecall_pre, the room below the window and the window's presence (RtDefs.v ecall_pre_stk w). *)
Lemma aj_gx_ecall_pre : forall w G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  ESTACK <= w -> spZ regsc mod 16 = 0 -> sp0 - STK <= spZ regsc - w -> spZ regsc <= sp0 ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_pre segs B lyc Sc W regsc memc mdc /\ ly_stk_lo lyc + w <= spZ regsc /\
  (forall a, spZ regsc - w <= a < spZ regsc -> apresent (w_H W) memc a).
Proof.
intros w G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc HJX Hw H16 Hlo Hhi Hra Hgp Htp.
destruct HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hwin : forall a, spZ regsc - w <= a < spZ regsc -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres; lia).
split; [|split; [rewrite Eslo; lia | exact Hwin]].
split; [exact HAR|]. split; [exact Hra|]. split; [exact H16|].
split; [rewrite Eslo; lia|]. split; [rewrite Eshi; lia|].
split; [intros a Ha; apply Hwin; lia|]. split; [exact Hgp | exact Htp].
Qed.

(* The step through a runtime entry whose post is of the standard shape: it returns to ra with the allocator state
   of the call, keeps every byte the walk sees outside its scratch window [spZ regsT - w, spZ regsT) and its cells
   Eb, and keeps every present byte present. The cells Eb are bytes the journal lets a callee write. *)
Lemma aj_gx_call_at : forall w (Eb : Z -> Prop) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    raw (P : bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= w -> sp0 - STK <= spZ regsT - w -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, Eb a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  (forall regs' mem' md', P regs' mem' md' ->
     AR segs B lyc Sc W mem' md' /\ same_but_materialized mdc md' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - w <= a < spZ regsT) -> ~ Eb a ->
        aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a)) ->
  SRr segs W (cfg_at segs pc regsT memT mdc)
    (fun W' c' => W' = W /\ exists regs' mem' md', c' = cfg_at segs (raZ regsT) regs' mem' md' /\ P regs' mem' md') ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       P regs2 mem2 md2).
Proof.
intros w Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw P
  HG HJX Hw Hlo Hhi Hraw HEb HX HC.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HP).
destruct (HX regs2 mem2 md2 HP) as (HAR2 & Hsame & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hraw; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|exact HP].
apply (ajournal_gx_after_write G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (spZ regsT - w <= a < spZ regsT) \/ Eb a) HG HJX).
- intros a Ha Hn. apply (Hfr a Ha); intros H'; apply Hn; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha].
  + left. split; [left; lia | lia].
  + exact (HEb a Ha).
- exact HAR2.
Qed.

(* aj_gx_call_at for an entry whose post returns at another FP state: the post's return config is built at the FP
   state fx' it names (`@cfg_at fx'`), and the lift returns the same fx'. Everything P must give is at the section's
   FP state (AR, the views): only the config changes. The printf-family contracts (snprintf, vfprintf, fprintf)
   have this post: f registers but f10 kept, rounding mode 0, which P carries. *)
Lemma aj_gx_call_atF : forall w (Eb : Z -> Prop) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    raw (P : YK11.FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= w -> sp0 - STK <= spZ regsT - w -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, Eb a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  (forall fx' regs' mem' md', P fx' regs' mem' md' ->
     AR segs B lyc Sc W mem' md' /\ same_but_materialized mdc md' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - w <= a < spZ regsT) -> ~ Eb a ->
        aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a)) ->
  SRr segs W (cfg_at segs pc regsT memT mdc)
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs (raZ regsT) regs' mem' md' /\ P fx' regs' mem' md') ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       P fx' regs2 mem2 md2).
Proof.
intros w Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw P
  HG HJX Hw Hlo Hhi Hraw HEb HX HC.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HP).
destruct (HX fx' regs2 mem2 md2 HP) as (HAR2 & Hsame & Hfr & Hpres2).
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hraw; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|exact HP].
apply (ajournal_gx_after_write G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (spZ regsT - w <= a < spZ regsT) \/ Eb a) HG HJX).
- intros a Ha Hn. apply (Hfr a Ha); intros H'; apply Hn; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha].
  + left. split; [left; lia | lia].
  + exact (HEb a Ha).
- exact HAR2.
Qed.

(* aj_gx_call_atF with presence asked only at or above alloc_ceiling, and each written byte of Eb visible after the
   call: the form of a printf-family post whose destination lies in the image (snprintf into g_names, 0x82b14). *)
Lemma aj_gx_call_atFo : forall w (Eb : Z -> Prop) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    raw (P : YK11.FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= w -> sp0 - STK <= spZ regsT - w -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, Eb a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  (forall fx' regs' mem' md', P fx' regs' mem' md' ->
     AR segs B lyc Sc W mem' md' /\ same_but_materialized mdc md' /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - w <= a < spZ regsT) -> ~ Eb a ->
        aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
     (forall a, Eb a -> aview segs (w_H W) mem' a <> None) /\
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> apresent (w_H W) memT a -> apresent (w_H W) mem' a)) ->
  SRr segs W (cfg_at segs pc regsT memT mdc)
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs (raZ regsT) regs' mem' md' /\ P fx' regs' mem' md') ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
       c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       P fx' regs2 mem2 md2).
Proof.
intros w Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw P
  HG HJX Hw Hlo Hhi Hraw HEb HX HC.
pose proof HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (E47 : 2 ^ 47 < 2 ^ 64) by (unfold Z.lt; reflexivity).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & HP).
destruct (HX fx' regs2 mem2 md2 HP) as (HAR2 & Hsame & Hfr & HEbv & Hoff).
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hraw; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [|exact HP].
apply (ajournal_gx_after_write_off G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (spZ regsT - w <= a < spZ regsT) \/ Eb a) HG HJX).
- intros a Ha Hn. apply (Hfr a Ha); intros H'; apply Hn; [left | right]; exact H'.
- intros a Ha Hv Hn.
  destruct (Z_le_gt_dec (spZ regsT - w) a) as [H1 | H1]; [destruct (Z_lt_le_dec a (spZ regsT)) as [H2 | H2]|].
  + assert (Hp : apresent (w_H W) mem2 a) by (apply Hoff; [lia | apply Hpres; lia]).
    exact (aview_some_of_apresent segs (w_H W) mem2 a Hp Hn).
  + assert (HnE : ~ Eb a) by (intros He; exact (HEbv a He Hn)).
    apply Hv. rewrite <- (Hfr a Ha ltac:(lia) HnE). exact Hn.
  + assert (HnE : ~ Eb a) by (intros He; exact (HEbv a He Hn)).
    apply Hv. rewrite <- (Hfr a Ha ltac:(lia) HnE). exact Hn.
- exact Hoff.
- exact Hsame.
- intros a [Ha | Ha].
  + left. split; [left; lia | lia].
  + exact (HEb a Ha).
- exact HAR2.
Qed.

(* A destination byte of a checked copy / fill the journal admits: an awr_byte of the journal's own window (not an
   out-cell byte), a writable byte of G, or an out cell. Each is writable and not the runtime's. *)
Lemma aj_gx_dest_byte : forall G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
  (inG G a /\ writable_at segs (mrestrict (w_H W) memc) a) \/ (inFP OUT a /\ sp0 <= a < sp0 + XO) ->
  writable_at segs (mrestrict (w_H W) memc) a /\ ~ aowned B lyc Sc a.
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k a HG HJX Ha.
destruct HJX as (HSTK & HXO & (memS & HJ & _) & _).
pose proof HJ as (HAR & _).
assert (Hw : forall b, awr_byte (STK + XO) (sp0 + XO) FP (ablocks B ly S) (ablocks B lyc Sc) lyc own b ->
  writable_at segs (mrestrict (w_H W) memc) b /\ ~ aowned B lyc Sc b).
{ intros b Hb. destruct (awr_byte_present segs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b HJ Hb) as [Hp Hno].
  split; [apply apresent_writable; exact Hp | exact Hno]. }
destruct Ha as [[Haw _] | [[HGa Hwr] | [_ Hwin]]].
- apply Hw. destruct Haw as [Hs | Hrest]; [left; lia | right; exact Hrest].
- split; [exact Hwr|]. intros Ho. destruct (HG a HGa) as [Hi Hns].
  exact (Hns (proj1 (al_owned_image _ _ LAWS _ _ _ _ _ a HAR Hi) Ho)).
- apply Hw. left. lia.
Qed.

(* THE CHECKED COPY / FILL INTO THE JOURNAL: aj_intrin_atS (YC85G.v:243) over ajournal_gx, at any G. A destination
   byte is an awr_byte outside the call's window (as aj_intrin_atS asks), a writable byte of G (it is outside the
   window: G is below the stack), or an out cell (above the call's sp). *)
Lemma aj_gx_intrin_at : forall op pc, aintrin_realizes segs B op pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO) /\
      ~ (spZ regsT - ESTACK <= a < spZ regsT)) \/
     (inG G a /\ writable_at segs (mrestrict (w_H W) memT) a) \/
     (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  amem_range d n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\
             amem_range x n /\ range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\
             (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
   | OSet => True end) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
       (forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
          match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros op pc AI G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n raw
  HG HJX Ha0 Ha1 Ha2 Hn Hd0 Hdn H16 Hlo Hhi Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (aj_gx_ecall_pre ESTACK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & _ & _).
assert (Hceil : alloc_ceiling <= sp0 - STK).
{ destruct HJX as (HSTK & HXO & (memS & HJ & _) & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (_ & _ & Hc & Hslo & _). lia. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha.
  destruct (aj_gx_dest_byte G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k a HG HJX) as [Hw Hno].
  { destruct (Hdest a Ha) as [(H1 & H2 & _) | [H1 | H1]];
    [left; split; assumption | right; left; exact H1 | right; right; exact H1]. }
  split; [exact Hw|]. split; [exact Hno|].
  destruct (Hdest a Ha) as [(_ & _ & H3) | [(HGa & _) | (_ & Hwin)]].
  - exact H3.
  - destruct (HG a HGa) as [Hi _]. pose proof (segs_low a Hi). lia.
  - lia. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (ajournal_gx_after_write G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (spZ regsT - ESTACK <= a < spZ regsT)) HG HJX).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha].
    + destruct (Hdest a Ha) as [(H1 & H2 & _) | [(H1 & _) | H1]];
      [left; split; assumption | right; left; exact H1 | right; right; exact H1].
    + left. split; [left; lia | lia].
  - exact HAR2. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hsame].
Qed.

(* The step through a runtime entry whose contract is RtDefs.v's art_post: fuzz_command's aj_art_at (lib/A/Prog/
   PaArt.v) over ajournal_gx, with the entry's cells Eb bytes the journal lets a callee write (G included). *)
Lemma aj_gx_art_at : forall stk (Eb : Z -> Prop) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
    raw (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  0 <= stk -> sp0 - STK <= spZ regsT - stk -> spZ regsT <= sp0 ->
  getr regsT 1 = raw ->
  (forall a, Eb a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 <= a < sp0 + XO)) \/
     inG G a \/ (inFP OUT a /\ sp0 <= a < sp0 + XO)) ->
  SRr segs W (cfg_at segs pc regsT memT mdc) (art_post segs B stk lyc Sc W regsT memT mdc Eb Qr) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - stk <= a < spZ regsT) -> ~ Eb a ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros stk Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw Qr
  HG HJX Hstk Hlo Hhi Hraw HEb HC.
eapply SRr_mono.
{ apply (aj_gx_call_at stk Eb pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k raw
    (fun regs' mem' md' => AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
       same_but_materialized mdc md' /\ Qr regs' mem' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ ascratch_stk stk regsT a -> ~ Eb a ->
          aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a) /\
       (forall a, ascratch_stk stk regsT a -> apresent (w_H W) mem' a))
    HG HJX Hstk Hlo Hhi Hraw HEb).
  - intros regs' mem' md' (HAR' & _ & Hs & _ & Hf & Hp & _).
    split; [exact HAR'|]. split; [exact Hs|]. split; [|exact Hp].
    intros a Ha Hw He. exact (Hf a Ha Hw He).
  - exact HC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & _ & HQ & Hfr & Hpres2 & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw He; exact (Hfr a Ha Hw He) | exact Hpres2].
Qed.
End b.

(* The string wrappers, each over its contract (lib/Rt/StrnlenDef.v, lib/A/Rt/RtString.v). The
   window of each call is its contract's; each wrapper writes only its window. *)
Section w.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* wrapper_strnlen over lib/Rt/StrnlenDef.v astrnlen_whole_realizesM (the whole buffer [x, x + n) checked and
   present; the answer is the first NUL index within n, or n; window 2 * ESTACK). *)
Lemma aj_gx_strnlen_at : forall lo hi pc, astrnlen_whole_realizesM segs B lo hi pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  src_ok segs W regsT memT x n -> (forall a, x <= a < x + n -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range x n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  consts_view segs lo hi W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (exists j, first_byte segs W memT x n 0 j /\ getr regs2 10 = w64 j) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros lo hi pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hn Hnr Hx0 Hxn Hsrc Hwin Hamr Hrad Hhull Hcv.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (aj_gx_ecall_pre segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & Hlo2 & Hwin2).
eapply SRr_mono.
{ apply (aj_gx_call_at segs B LAWS segs_low (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' mem' md' => AR segs B lyc Sc W mem' md' /\ aregs_preserved regsT regs' /\
       same_but_materialized mdc md' /\
       (exists j, first_byte segs W memT x n 0 j /\ getr regs' 10 = w64 j) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem' a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - intros regs' mem' md' (HAR' & _ & Hs & _ & Hf & Hp).
    split; [exact HAR'|]. split; [exact Hs|]. split; [|exact Hp].
    intros a Ha Hw _. exact (Hf a Ha Hw).
  - exact (HC lyc Sc W regsT memT mdc x n HPRE Hlo2 Hwin2 Hx Hn Hnr Hx0 Hxn Hsrc Hwin Hamr Hrad Hhull Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & _ & HP & _ & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* wrapper_strlen over lib/A/Rt/RtString.v astrlen_realizes (window ESTACK). *)
Lemma aj_gx_strlen_at : forall pc, RtString.astrlen_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> 0 < x ->
  astr_at segs W memT x s ->
  aread_ok segs ESTACK W regsT memT x (astr_len s + 1) ->
  atail_vis segs W memT (x + astr_len s) ->
  rt_rom_view segs B W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (astr_len s) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x s raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hx0 Hstr Hrd Htail Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre segs B ESTACK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_gx_art_at segs B LAWS segs_low ESTACK (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md
    own lyc Sc mdc k raw (fun regs' _ => getr regs' 10 = w64 (astr_len s)) HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - exact (HC lyc Sc W regsT memT mdc x s HPRE Hx Hx0 Hstr Hrd Htail Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H)) | exact Hpres2].
Qed.

(* wrapper_strncmp over lib/A/Rt/RtString.v astrncmp_realizes (window 2 * ESTACK). *)
Lemma aj_gx_strncmp_at : forall pc, RtString.astrncmp_realizes segs B pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - 2 * ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 < x -> 0 < y ->
  astr_at segs W memT x sx -> astr_at segs W memT y sy ->
  aread_ok segs (2 * ESTACK) W regsT memT x (Z.min n (astr_len sx + 1)) -> amem_range x (astr_len sx + 8) ->
  aread_ok segs (2 * ESTACK) W regsT memT y (Z.min n (astr_len sy + 1)) -> amem_range y (astr_len sy + 8) ->
  atail_vis segs W memT (x + astr_len sx) -> atail_vis segs W memT (y + astr_len sy) ->
  rt_rom_view segs B W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (getr regs2 10 = w64 0 <->
        LStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n sx sy raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hy Hn Hnr Hx0 Hy0 Hsx Hsy Hrx Hmx Hry Hmy Htx Hty Hrom.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre segs B (2 * ESTACK) G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT HJX
  ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as HPRE.
eapply SRr_mono.
{ apply (aj_gx_art_at segs B LAWS segs_low (2 * ESTACK) (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S W0
    mem md own lyc Sc mdc k raw
    (fun regs' _ => getr regs' 10 = w64 0 <->
       LStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0)
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - exact (HC lyc Sc W regsT memT mdc x y n sx sy HPRE Hx Hy Hn Hnr Hx0 Hy0 Hsx Hsy Hrx Hmx Hry Hmy Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H)) | exact Hpres2].
Qed.
End w.
End a.

(* Link's instances: the G objects of link_aaddr.v's LA_G that link's own code writes through a checked copy, a
   checked fill or a wrapper (g_nl: fuzz_send +0xcc, kernel +0x1ee4, LLVMFuzzerTestOneInput +0x304;
   msg_build.long_alias: kernel +0xaf8; g_names: LLVMFuzzerTestOneInput's wrapper_snprintf at 0x82b14). *)
Section la.
Lemma inG_LA_G_NL : forall a, LA_G_NL <= a < LA_G_NL + 271992 -> inG LA_G a.
Proof.
intros a Ha. apply (inG_of_In LA_G LA_G_NL 271992 a); [|exact Ha].
unfold LA_G. cbn [In]. right; left; reflexivity.
Qed.
Lemma inG_LA_G_NAMES : forall a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> inG LA_G a.
Proof.
intros a Ha. apply (inG_of_In LA_G LA_G_NAMES 512 a); [|exact Ha].
unfold LA_G. cbn [In]. right; right; left; reflexivity.
Qed.
Lemma inG_LA_LONG_ALIAS : forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> inG LA_G a.
Proof.
intros a Ha. apply (inG_of_In LA_G LA_LONG_ALIAS 301 a); [|exact Ha].
unfold LA_G. cbn [In]. right; right; right; left; reflexivity.
Qed.

(* Every byte of those three objects is writable at image A's segments, at any memory: the premise
   `writable_at segs (mrestrict (w_H W) memT) a` of aj_gx_intrin_at / aj_gx_dest_byte for a byte of G. *)
Lemma wseg_LA_G_NL : wseg_ok tfibsegs (Z_to_bv 64 LA_G_NL) (Z.to_nat 271992) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_LA_G_NAMES : wseg_ok tfibsegs (Z_to_bv 64 LA_G_NAMES) (Z.to_nat 512) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wseg_LA_LONG_ALIAS : wseg_ok tfibsegs (Z_to_bv 64 LA_LONG_ALIAS) (Z.to_nat 301) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma LA_G_NL_writable : forall m a, LA_G_NL <= a < LA_G_NL + 271992 -> writable_at tfibsegs m a.
Proof. intros m. apply writable_at_of_wseg; [unfold LA_G_NL; lia | unfold LA_G_NL; lia | exact wseg_LA_G_NL]. Qed.
Lemma LA_G_NAMES_writable : forall m a, LA_G_NAMES <= a < LA_G_NAMES + 512 -> writable_at tfibsegs m a.
Proof. intros m. apply writable_at_of_wseg; [unfold LA_G_NAMES; lia | unfold LA_G_NAMES; lia | exact wseg_LA_G_NAMES]. Qed.
Lemma LA_LONG_ALIAS_writable : forall m a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> writable_at tfibsegs m a.
Proof.
intros m. apply writable_at_of_wseg; [unfold LA_LONG_ALIAS; lia | unfold LA_LONG_ALIAS; lia | exact wseg_LA_LONG_ALIAS].
Qed.
End la.
