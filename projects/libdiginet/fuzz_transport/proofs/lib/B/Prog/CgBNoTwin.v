(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/FP.v; 609 of its 651 lines of code are new or changed and 349 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/crtA_conv.v, with its module paths changed; 862 of its 968 lines of code are new or changed and 545 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/crtB_loop.v, with its module paths and module names changed; 213 of its 293 lines of code are new or changed and 888 lines of the source are left out. *)
(* CgBNoTwin: the facts the image-B walks of check_events_fields and check_refusal take that lib/B/Prog/DecodeFevt.v
   does not state: the image view of one byte, the bytes and the shadow of a live block, the footprint over a runtime
   cell and over a block, and the journal (lib/Reusable/YCbq.v ajournal) across a footprint run and across a call.
   Every name is function-neutral: a frame size, a stack window or a cell range is an argument, never a constant of
   one function. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YK06 YI00 YCbq.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YG0v YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportFevt.
Import ListNotations.
Open Scope Z_scope.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.

(* ---- the image view of one byte ---- *)

(* aview at a visible byte is decode's mrd of that byte. *)
Lemma cgb_aview_mrd : forall (H : word -> bool) mem a,
  H (wa a) = false ->
  aview tfibsegs H mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof.
  intros H mem a Hh. unfold wa in Hh.
  unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite Hh. reflexivity.
Qed.

Lemma cgb_opt_byte_eq : forall (x y : option byte),
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] E; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* Two equal views of a visible byte are the same mrd of that byte (the bytes themselves may differ where the
   memory holds none and the image does). *)
Lemma cgb_mrd_eq_of_aview : forall (H H' : word -> bool) mem mem' a,
  H (wa a) = false -> H' (wa a) = false ->
  aview tfibsegs H' mem' a = aview tfibsegs H mem a ->
  mrd rsegs mem' (wa a) = mrd rsegs mem (wa a).
Proof.
  intros H H' mem mem' a Hh Hh' E. apply cgb_opt_byte_eq.
  rewrite <- (cgb_aview_mrd H' mem' a Hh'), <- (cgb_aview_mrd H mem a Hh). exact E.
Qed.

Lemma cgb_bytes_at_kept : forall (H H' : word -> bool) mem mem' A bs,
  bytes_at rsegs mem A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> H (wa a) = false /\ H' (wa a) = false /\
     aview tfibsegs H' mem' a = aview tfibsegs H mem a) ->
  bytes_at rsegs mem' A bs.
Proof.
  intros H H' mem mem' A bs (HA & Hlen & Hb) Hk.
  split; [exact HA|]. split; [exact Hlen|].
  intros i Hi.
  destruct (Hk (A + Z.of_nat i) ltac:(lia)) as (Hh & Hh' & Ha).
  rewrite (cgb_mrd_eq_of_aview H H' mem mem' (A + Z.of_nat i) Hh Hh' Ha). exact (Hb i Hi).
Qed.

(* The image view at one byte depends on that byte of the memory only (for YI00.v garr8_frame). *)
Lemma cgb_mbyte_same : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  YP09.mbyte tfibsegs (mrestrict H m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof. intros H m m' a E. unfold YP09.mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.

(* ---- small arithmetic facts ---- *)

Lemma cgb_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]. Qed.

Lemma cgb_u8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma cgb_mem_grows_restrict : forall (H : word -> bool) m m',
  YK1b.mem_grows m m' -> YK1b.mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' HG x Hx. unfold mrestrict in Hx |- *.
  destruct (H x); [exact Hx | exact (HG x Hx)].
Qed.

(* A byte of application memory has its shadow byte below the start of high application memory, so a write to a
   stack window there or above keeps the whole shadow map of the application: addressable survives such a write. *)
Lemma cgb_shadow_below_high : forall a,
  BCells.app_mem a -> 0 <= BCells.shadow_addr a < BCells.HIGHMEM_BEG.
Proof.
  intros a Ha.
  unfold BCells.app_mem, BCells.LOWMEM_END, BCells.HIGHMEM_BEG, BCells.APPMEM_END in Ha.
  unfold BCells.shadow_addr, BCells.ASAN_K, BCells.HIGHMEM_BEG.
  destruct Ha as [Ha|Ha]; Z.div_mod_to_equations; lia.
Qed.

Lemma cgb_addressable_munch : forall (m m' : word -> option byte) p n lo hi,
  BCells.addressable m p n -> munch [(lo, hi)] m m' ->
  BCells.HIGHMEM_BEG <= lo -> hi <= 2 ^ 64 ->
  BCells.addressable m' p n.
Proof.
  intros m m' p n lo hi (Hp & Hn & Htop & HA) MU Hlo Hhi.
  split; [exact Hp|]. split; [exact Hn|]. split; [exact Htop|].
  intros i Hi. destruct (HA i Hi) as (Happ & b & Hb & Hok).
  pose proof (cgb_shadow_below_high (p + i) Happ) as Hsh.
  split; [exact Happ|]. exists b. split; [|exact Hok].
  assert (Hout : BCells.shadow_addr (p + i) < lo \/ hi <= BCells.shadow_addr (p + i)) by (left; lia).
  assert (Hr : 0 <= BCells.shadow_addr (p + i) < 2 ^ 64) by (unfold BCells.HIGHMEM_BEG in Hsh; lia).
  exact (mrd_tp m m' lo hi (BCells.shadow_addr (p + i)) b MU Hr Hout Hb).
Qed.

(* ---- the runtime cells ---- *)

(* A runtime cell lies in a loaded segment, which no world hides, so the walk's footprint holds it. *)
Lemma cgb_cell_rng : forall (W : world tfibsegs) a n,
  decode_seg_covers a n = true -> a + n <= 2 ^ 64 ->
  ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a n.
Proof.
  intros W a n Hc Ht.
  apply (decode_rng_vis W a n (decode_covers_lo a n Hc) Ht).
  intros i Hi. exact (decode_covers_visible (w_H W) a n i (w_Hoff W) Hc Hi Ht).
Qed.

(* ---- a live block: its bytes, its shadow bytes, and the footprint over both ---- *)

Section CgBBlocks.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

(* A byte the reader sees outside the image is present in the memory and not hidden. *)
Lemma cgb_aview_some : forall (H : word -> bool) (mem : word -> option byte) s v,
  0 <= s < 2 ^ 64 -> ~ in_img segs s -> aview segs H mem s = Some v ->
  H (Z_to_bv 64 s) = false /\ exists b, mem (Z_to_bv 64 s) = Some b /\ bv_unsigned b = v.
Proof.
  intros H mem s v Hs Hn Hv.
  destruct (aview_byte segs H mem s v Hv) as (b & Hb & -> & _).
  pose proof (seg_rom_none segs s Hs Hn) as Er.
  unfold YP09.mbyte, mrestrict in Hb. cbv beta in Hb.
  revert Hb. destruct (H (Z_to_bv 64 s)) eqn:EH; intros Hb.
  - rewrite Er in Hb. cbn in Hb. discriminate.
  - split; [reflexivity|]. revert Hb. destruct (mem (Z_to_bv 64 s)) as [b'|] eqn:Em; intros Hb.
    + cbn in Hb. injection Hb as ->. exists b. split; reflexivity.
    + rewrite Er in Hb. cbn in Hb. discriminate.
Qed.

Lemma cgb_aview_same : forall (H : word -> bool) (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview segs H m' a = aview segs H m a.
Proof. intros H m m' a E. unfold aview, YP09.mbyte, mrestrict. cbv beta. rewrite E. reflexivity. Qed.

(* The shadow byte of a byte of a live block: visible, present, and saying the byte is addressable
   (AsanCells.shadow_ok). *)
Lemma cgb_shadow_byte : forall ly S (W : world segs) mem md p n a,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  w_H W (Z_to_bv 64 (BCells.shadow_addr a)) = false /\
  exists b, mem (Z_to_bv 64 (BCells.shadow_addr a)) = Some b /\ BCells.shadow_ok a (bv_signed b).
Proof.
  intros ly S W mem md p n a LAWS HAR Hin Ha.
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as ((Hp8 & HN0 & HS) & _).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & _).
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  set (N := req_size n) in *.
  assert (HNp : 0 < N) by lia.
  assert (Hg : 0 <= (a - p) / 8 < (N + 7) / 8) by (Z.div_mod_to_equations; lia).
  specialize (HS _ Hg).
  assert (Es : YG0v.shadow_of_addr SHADOW_OFF p + (a - p) / 8 = BCells.shadow_addr a).
  { unfold YG0v.shadow_of_addr, BCells.shadow_addr, SHADOW_OFF, BCells.ASAN_K. Z.div_mod_to_equations. lia. }
  rewrite Es in HS.
  assert (Hsa : 0 <= BCells.shadow_addr a < 2 ^ 64)
    by (unfold BCells.shadow_addr, BCells.ASAN_K; Z.div_mod_to_equations; lia).
  assert (Hni : ~ in_img segs (BCells.shadow_addr a)).
  { intros Hi. pose proof (decode_segs_low _ Hi) as Hl. rewrite C5 in Hl.
    unfold BCells.shadow_addr, BCells.ASAN_K in Hl. Z.div_mod_to_equations. lia. }
  destruct (cgb_aview_some (w_H W) mem _ _ Hsa Hni HS) as (Hh & b & Hb & Ev).
  split; [exact Hh|]. exists b. split; [exact Hb|].
  assert (Hv7 : 0 <= (if (a - p) / 8 <? N / 8 then 0 else N mod 8) < 8)
    by (destruct ((a - p) / 8 <? N / 8); [lia | apply Z.mod_pos_bound; lia]).
  unfold BCells.shadow_ok.
  rewrite (decode_signed_small b) by (rewrite Ev; lia). rewrite Ev.
  destruct ((a - p) / 8 <? N / 8) eqn:Eg; [left; reflexivity|].
  apply Z.ltb_ge in Eg.
  destruct (Z.eq_dec (N mod 8) 0) as [Z0|NZ]; [left; exact Z0|right].
  split; [|lia]. Z.div_mod_to_equations. lia.
Qed.

(* A window of a live block is addressable in decode's form. *)
Lemma cgb_addressable : forall ly S (W : world segs) mem md p n x len,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 <= len -> x + len <= p + req_size n -> BCells.addressable mem x len.
Proof.
  intros ly S W mem md p n x len LAWS HAR Hin Hx Hl Hxl.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & _).
  pose proof asan_consts as (C1 & _).
  unfold BCells.addressable. split; [lia|]. split; [exact Hl|].
  split; [unfold BCells.APPMEM_END; lia|].
  intros i Hi. unfold BCells.addr_byte. split.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold BCells.app_mem, BCells.LOWMEM_END, BCells.HIGHMEM_BEG, BCells.APPMEM_END. lia.
  - destruct (cgb_shadow_byte ly S W mem md p n (x + i) LAWS HAR Hin ltac:(lia)) as (_ & b & Hb & Hok).
    exists b. split; [unfold mrd, wa; rewrite Hb; reflexivity | exact Hok].
Qed.

(* Every byte of a window of a live block, and its shadow byte, is inside the walk's footprint
   (every visible byte). *)
Lemma cgb_rng_shadow : forall ly S (W : world segs) mem md p n x len,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> x + len <= p + req_size n ->
  forall i, 0 <= i < len ->
    ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) (BCells.shadow_addr (x + i)) 1.
Proof.
  intros ly S W mem md p n x len LAWS HAR Hin Hx Hxl i Hi.
  destruct (cgb_shadow_byte ly S W mem md p n (x + i) LAWS HAR Hin ltac:(lia)) as (Hh & _).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & _).
  pose proof asan_consts as (C1 & _).
  apply decode_rng_vis.
  - unfold BCells.shadow_addr, BCells.ASAN_K. Z.div_mod_to_equations. lia.
  - unfold BCells.shadow_addr, BCells.ASAN_K. Z.div_mod_to_equations. lia.
  - intros j Hj. replace (BCells.shadow_addr (x + i) + j) with (BCells.shadow_addr (x + i)) by lia. exact Hh.
Qed.

Lemma cgb_rng_block : forall ly S (W : world segs) mem md p n x len,
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> 0 <= len -> x + len <= p + req_size n ->
  ExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) x len.
Proof.
  intros ly S W mem md p n x len LAWS HAR Hin Hx Hl Hxl.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & Hpres & _).
  pose proof asan_consts as (C1 & _).
  apply decode_rng_vis; [lia | lia|].
  intros j Hj. exact (proj1 (proj1 (Hpres (x + j) ltac:(lia)))).
Qed.

(* The bytes of a live block, in decode's form, from the window's reader fact (YI00.v garr8). *)
Lemma cgb_bytes_at_of_block : forall ly S (W : world segs) mem md p n x (l : list Z),
  AR_laws segs B -> AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= x -> x + Z.of_nat (length l) <= p + req_size n ->
  garr8 segs (mrestrict (w_H W) mem) x l ->
  bytes_at rsegs mem x (map (fun z => Z_to_bv 8 z) l).
Proof.
  intros ly S W mem md p n x l LAWS HAR Hin Hx Hxl HG.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hp16 & Hp4096 & Hpc & Happ & Hpres & _).
  pose proof asan_consts as (C1 & _).
  split; [lia|]. split; [rewrite length_map; lia|].
  intros i Hi. rewrite length_map in Hi.
  pose proof (garr8_mbyte segs (mrestrict (w_H W) mem) x l i HG Hi) as HV.
  assert (Hh : w_H W (Z_to_bv 64 (x + Z.of_nat i)) = false).
  { destruct (Hpres (x + Z.of_nat i) ltac:(lia)) as ((Hh & _) & _). exact Hh. }
  unfold YP09.mbyte, mrestrict in HV. cbv beta in HV. rewrite Hh in HV.
  rewrite (nth_error_nth' (map (fun z => Z_to_bv 8 z) l) (Z_to_bv 8 0))
    by (rewrite length_map; exact Hi).
  rewrite (map_nth (fun z => Z_to_bv 8 z) l 0 i).
  exact HV.
Qed.
End CgBBlocks.

(* ---- the journal across a footprint run and across a call ---- *)

Section CgBJournal.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation sink := YE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation AJ := (@ajournal rc sink segs B).

(* The conjuncts of a journal (YCbq.v ajournal) a walk reads. *)
Lemma cgb_j : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  AJ STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  AR segs B ly' S' W' mem' md' /\ layout_le (length (st_secs S)) ly ly' /\
  frames S' = own ++ frames S /\ st_nev S' <= st_nev S + k /\
  (forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  astk_ok STK ly sp0.
Proof.
  intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
    (H1 & H2 & _ & _ & _ & H6 & H7 & _ & H9 & _ & _ & _ & _ & H14 & H15 & _ & _).
  exact (conj H1 (conj H2 (conj H6 (conj H7 (conj H9 (conj H14 H15)))))).
Qed.

(* A footprint run that writes nothing moves the journal only by the materialized model. *)
Lemma cgb_j_sbm : AR_laws segs B -> forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc',
  AJ STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> same_but_materialized mdc mdc' ->
  AJ STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc' k.
Proof.
  intros LAWS STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k mdc' HJ Hs.
  apply (@ajournal_exec rc sink segs B LAWS decode_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k
           memc mdc' (fun _ => False) HJ).
  - intros x _. reflexivity.
  - intros x Hx. exact Hx.
  - intros x _. reflexivity.
  - exact Hs.
  - intros a [].
Qed.

(* The journal across a footprint run that writes only the window [sp - F, sp) of its own stack frame
   (the frame size F and the stack window STK are arguments). *)
Lemma cgb_j_frame : AR_laws segs B ->
  forall STK F lyc Sc W memc mdc (sp : Z) ly1 S1 W1 mem1 md1 k1 m' md',
  0 <= F <= STK ->
  AJ STK sp [] lyc Sc W memc mdc [] ly1 S1 W1 mem1 md1 k1 ->
  (forall x : word, ~ (sp - F <= bv_unsigned x < sp) -> m' x = mem1 x) ->
  YK1b.mem_grows mem1 m' -> same_but_materialized md1 md' ->
  AJ STK sp [] lyc Sc W memc mdc [] ly1 S1 W1 m' md' k1.
Proof.
  intros LAWS STK F lyc Sc W memc mdc sp ly1 S1 W1 mem1 md1 k1 m' md' HF HJ1 HOUT HGROW HSBM.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES1 & _ & _ & _).
  assert (HHIDOUT : forall x : word, w_H W1 x = true -> ~ (sp - F <= bv_unsigned x < sp)).
  { intros x Hx Hr.
    assert (Hw : sp - STK <= bv_unsigned x < sp) by lia.
    pose proof (HPRES1 (bv_unsigned x) Hw) as (Hh & _).
    rewrite Z_to_bv_bv_unsigned in Hh. rewrite Hh in Hx. discriminate. }
  assert (HFR2 : forall x : word, ~ (sp - F <= bv_unsigned x < sp) ->
      mrestrict (w_H W1) m' x = mrestrict (w_H W1) mem1 x)
    by (intros x Hx; unfold mrestrict; destruct (w_H W1 x); [reflexivity | exact (HOUT x Hx)]).
  assert (HGR2 : YK1b.mem_grows (mrestrict (w_H W1) mem1) (mrestrict (w_H W1) m'))
    by (apply cgb_mem_grows_restrict; exact HGROW).
  assert (HHID : forall x : word, w_H W1 x = true -> m' x = mem1 x)
    by (intros x Hx; apply HOUT; exact (HHIDOUT x Hx)).
  assert (HWB : forall a, (sp - F <= a < sp) ->
      awr_byte STK sp [] (ablocks B lyc Sc) (ablocks B ly1 S1) ly1 [] a)
    by (intros a Ha; unfold awr_byte; left; lia).
  eapply ajournal_exec with (Wr := fun a => sp - F <= a < sp);
    solve [ exact LAWS | exact decode_segs_low | exact HJ1 | exact HFR2 | exact HGR2 | exact HHID
          | exact HSBM | exact HWB ].
Qed.

(* The frame cells survive a call whose window lies below them, at any frame size F. *)
Lemma cgb_frame_across : forall (W1 W2 : world segs) ly1 S1 mem1 mem2 (E : Z -> Prop) slo shi A F cs,
  @acall_kept rc segs B ly1 S1 W1 mem1 W2 mem2 slo shi E ->
  rw_cells rsegs mem1 A cs -> Z.of_nat (cells_size cs) = F ->
  (forall a, A <= a < A + F -> apresent (w_H W1) mem1 a) ->
  YM05.alloc_ceiling <= A -> shi <= A -> A + F <= 2 ^ 64 ->
  rw_cells rsegs mem2 A cs.
Proof.
  intros W1 W2 ly1 S1 mem1 mem2 E slo shi A F cs HK HC Hsz HP Hce Hs Hhi.
  pose proof HK as (K1 & _ & _ & _ & K5 & _).
  apply (decode_rw_cells_eq mem1 mem2 A cs HC).
  rewrite Hsz. intros i Hi. pose proof (HP (A + i) ltac:(lia)) as HPa.
  assert (Hout : ~ (slo <= A + i < shi)) by lia.
  apply (decode_byte_eq (w_H W1) (w_H W2) mem1 mem2 (A + i) HPa).
  - exact (K5 (A + i) ltac:(lia) Hout HPa).
  - exact (K1 (A + i) ltac:(lia) Hout).
Qed.
End CgBJournal.
