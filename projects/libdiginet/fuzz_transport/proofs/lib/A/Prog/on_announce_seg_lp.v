(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names changed; 668 of its 739 lines of code are new or changed and 694 lines of the source are left out. *)
(* on_announce_seg_lp: Theorem onann_piece_lp : forall fx rc B MT, @onann_lp_stmt fx rc B MT (lib/A/Prog/OnannCut.v),
   the parse piece of the walk of on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce),
   code +0x20c .. +0x218 (0x87c80 .. 0x87c8c), from the parse cut onann_lp_at to the ignore cut onann_ign_at (+0x21c)
   and the personality cut onann_pf_at (+0x248):
     +0x20c .. +0x214  a0 = fp (`mv a0, s6`), a1 = a = F + 256 (`mv a1, s5`), `jal diginet_announce_parse`: one run
                       (TransportGRunA.v paj_run_x) from a state with no region;
     +0x214            diginet_announce_parse (0x8c238), the statement's transport_leaf_wr_at premise
                       (lib/A/Prog/diginet_announce_parse_cg.v) through TransportGCg.v gx_call_leaf and
                       DgnTransportLeafb.v decode_leafb_journal, with WR = [(a, a + 40)] on code 0 and [] else. Its
                       inputs at the call memory: cmd = fr_cmd b at f + 30 and body = buf + 30, body_len = fr_body_len b
                       at f + 32 (the 64 bytes trans_dframe_at gives at the entry, kept: on_announce_seg_kit.v
                       onann_src_kept; split by lp_f_split), the body bytes fr_body b at buf + 30 (garr8 of b at buf,
                       kept), a's 40 bytes (present; its shadow bytes 32 .. 36 are 0, so it is addressable:
                       TransportGNotice.v frame_ra_zero), and a apart from f's and the body's ranges (DgnTransportCg.v
                       trans_src_ok_disj_own);
     +0x218            `beqz a0`, taken up again from a state with no region (as SlostHead.v at +0x178): code 0 runs to
                       +0x248 and concludes by onann_pf_at (onann_ign b = false; a holds the parse's fields,
                       onann_a_ok, read off PAnn.ann_cells by lp_field_prefix and lp_rdword_le8), any other code runs
                       to +0x21c and concludes by onann_ign_at (onann_ign b = true).
   What the call keeps (acall_kept_g) crosses the leaf by TransportGFrame.v dk_kept_nfz_gw (the leaf's stack window
   lies in the call's, a's 40 bytes in the own frame) and the two runs by dk_kept_step_gw (they write no byte). The
   registers the cuts read are the cut's, kept by the runs and by the leaf (aregs_preserved). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  diginet_announce_parse_cg diginet_announce_parse_c DgnTransportLeafb DgnTransportCgRun LeafCgKit AsanKA
  TransportFevt TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells Step Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_announce_parse_c diginet_frame_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module LStep := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Module AImg0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Img0.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.AsanKA.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportLeafb.
Module CR := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.DgnTransportCgRun.
Module FFv := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportFevt.
Module LAP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_announce_parse_cg.
Module ADP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_announce_parse_c.
Module PAnn := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_announce_parse_c.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* +0x20c and +0x218, both with no region. *)
Definition LP_C2 : Z := AF_on_announce + 0x218.
Definition ss_lp1 : sstate := mkSS ONANN_LP sr_atoms [] None (mkFacts [] [] []).
Definition ss_lp2 : sstate := mkSS LP_C2 sr_atoms [] None (mkFacts [] [] []).
Definition LP_B0 : Z * Z := (0, 0).

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* `beqz a0` on the sign-extended code. *)
Lemma lp_eqb0 : forall v, - 2 ^ 31 <= v < 2 ^ 31 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof.
intros v Hv. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 0 (2 ^ 64)) by lia.
destruct (Z.eqb_spec v 0) as [-> | Hne]; [reflexivity|].
apply Z.eqb_neq. intros HH. apply Hne.
destruct (Z_lt_le_dec v 0) as [Hneg | Hpos].
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) in HH by lia. lia.
- rewrite (Z.mod_small v (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* The parse's code is -9, -4 or 0; 0 needs a body of 33 bytes or more. *)
Lemma lp_code_range : forall c l, - 2 ^ 31 <= DSpec.ann_code c l < 2 ^ 31.
Proof.
intros c l. unfold DSpec.ann_code.
destruct (negb (DSpec.ann_cmd c)); [lia|]. destruct (l <? 33); lia.
Qed.
Lemma lp_ok_len : forall c l, DSpec.ann_code c l = 0 -> 33 <= l.
Proof.
intros c l. unfold DSpec.ann_code.
destruct (negb (DSpec.ann_cmd c)); [discriminate|]. destruct (Z.ltb_spec l 33); [discriminate | lia].
Qed.

(* A frame the parse accepted: the body's length is body_len, inside b from 30. *)
Lemma lp_body_len : forall b, DSpec.fr_code b = 0 ->
  0 <= DSpec.fr_body_len b /\ 30 + DSpec.fr_body_len b <= Z.of_nat (length b) /\
  Z.of_nat (length (DSpec.fr_body b)) = DSpec.fr_body_len b.
Proof.
intros b H. destruct (DSpec.fr_code_ok b H) as (L & _ & N1 & N2).
unfold DSpec.fr_body, DSpec.fr_body_len. rewrite length_firstn, length_skipn. lia.
Qed.

(* The strings the notices read (TSess.v ann_field) are prefixes of the fields copy_strz writes. *)
Lemma lp_field_prefix : forall src old,
  DSpec.copy_strz 10 9 src old = TSS.ann_field src ++ skipn (S (DSpec.copy_len 10 9 src)) old.
Proof. intros src old. unfold DSpec.copy_strz, TSS.ann_field. rewrite <- app_assoc. reflexivity. Qed.

Lemma lp_ann_field_len : forall src, (length (TSS.ann_field src) <= 10)%nat.
Proof.
intros src. unfold TSS.ann_field, DSpec.copy_len. rewrite length_app, length_firstn. cbn [length].
pose proof (DSpec.nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as H. rewrite length_firstn in H. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Bytes through the view and raw                                   *)
(* ------------------------------------------------------------------ *)

(* Equal views give equal image bytes. *)
Lemma lp_mbyte_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [x|], (mbyte tfibsegs (mrestrict H m) a) as [y|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A byte array is kept by a memory whose view keeps its bytes. *)
Lemma lp_garr8_view : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H m) p l -> garr8 tfibsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l E G. apply (garr8_frame tfibsegs (mrestrict H m) (mrestrict H' m') p l G).
intros a Ha. apply lp_mbyte_aview. exact (E a Ha).
Qed.

Lemma lp_garr8_cons : forall (mm : word -> option byte) p x l,
  garr8 tfibsegs mm p (x :: l) -> garr8 tfibsegs mm p [x] /\ garr8 tfibsegs mm (p + 1) l.
Proof.
intros mm p x l G. destruct (proj1 (garr8_app tfibsegs mm p [x] l) G) as [G1 G2].
split; [exact G1|]. replace (p + 1) with (p + Z.of_nat (length [x])) by (cbn; lia). exact G2.
Qed.

(* f's 64 bytes as the parse left them (fr_code b = 0): 30 bytes, then cmd, ncmds, body and body_len. *)
Lemma lp_fbytes_split : forall buf (b fj : list byte), (30 <= length b)%nat -> length fj = 64%nat ->
  exists pre post : list byte, length pre = 30%nat /\
  LCells.cells_bytes (PParse.parse_cells buf b fj) =
    pre ++ DSpec.b8 (DSpec.fr_cmd b) :: DSpec.b8 (DSpec.fr_ncmds b) ::
      (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b))) ++ post.
Proof.
intros buf b fj Hb Hfj.
exists (DSpec.fr_dst b ++ DSpec.fr_src b ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_ethertype b)) ++
        firstn 2 (skipn 14 fj) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_numbytes b)) ++
        LMem.le2 (Z_to_bv 64 (DSpec.fr_sum b)) ++ LMem.le4 (Z_to_bv 64 (DSpec.fr_send b)) ++
        LMem.le4 (Z_to_bv 64 (DSpec.fr_ack b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_retry b))).
exists (LMem.le8 (Z_to_bv 64 (DSpec.fr_pad_len b)) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_body_sum b)) ++
        [DSpec.b8 (if DSpec.fr_sum b =? DSpec.fr_body_sum b then 1 else 0)] ++ skipn 59 fj ++ []).
split.
- unfold DSpec.fr_dst, DSpec.fr_src.
  rewrite !length_app, !length_firstn, !length_skipn, !LMem.length_le2, !LMem.length_le4. lia.
- unfold PParse.parse_cells. cbn [LCells.cells_bytes LCells.cbytes]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma lp_f_split : forall (mm : word -> option byte) fp buf (b fj : list byte),
  DSpec.fr_code b = 0 -> length fj = 64%nat ->
  garr8 tfibsegs mm fp (frame_f_bytes buf b fj) ->
  garr8 tfibsegs mm (fp + 30) (map (fun x : byte => bv_unsigned x) [DSpec.b8 (DSpec.fr_cmd b)]) /\
  garr8 tfibsegs mm (fp + 32) (map (fun x : byte => bv_unsigned x)
    (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b)))).
Proof.
intros mm fp buf b fj Hc Hfj G.
destruct (DSpec.fr_code_ok b Hc) as (L30 & _).
unfold frame_f_bytes, frame_f_cells in G. rewrite Hc in G. cbn [Z.eqb] in G.
destruct (lp_fbytes_split buf b fj L30 Hfj) as (pre & post & Lp & E).
rewrite E, map_app in G. apply garr8_app in G. destruct G as [_ G].
rewrite length_map, Lp in G. cbn [map] in G.
apply lp_garr8_cons in G. destruct G as [G30 G].
apply lp_garr8_cons in G. destruct G as [_ G].
rewrite map_app in G. apply garr8_app in G. destruct G as [G32 _].
split.
- exact G30.
- replace (fp + 32) with (fp + Z.of_nat 30 + 1 + 1) by (cbn; lia). exact G32.
Qed.

(* The body bytes fr_body b at buf + 30, from b's bytes at buf. *)
Lemma lp_body_garr8 : forall (mm : word -> option byte) buf (b : list byte),
  DSpec.fr_code b = 0 -> garr8 tfibsegs mm buf (TW.zs b) ->
  garr8 tfibsegs mm (buf + 30) (map (fun x : byte => bv_unsigned x) (DSpec.fr_body b)).
Proof.
intros mm buf b Hc G.
destruct (DSpec.fr_code_ok b Hc) as (L30 & _).
assert (Eb : b = firstn 30 b ++ DSpec.fr_body b ++ skipn (Z.to_nat (DSpec.fr_body_len b)) (skipn 30 b)).
{ unfold DSpec.fr_body. rewrite !firstn_skipn. reflexivity. }
unfold TW.zs in G. rewrite Eb in G. rewrite !map_app in G.
apply garr8_app in G. destruct G as [_ G]. apply garr8_app in G. destruct G as [G _].
rewrite length_map, length_firstn in G. replace (Nat.min 30 (length b)) with 30%nat in G by lia.
exact G.
Qed.

(* An eight-byte cell the leaf leaves (raw bytes le8 v), read through the view. *)
Lemma lp_rdword_le8 : forall (H : word -> bool) (m : word -> option byte) a v,
  (forall i, 0 <= i < 8 -> H (Z_to_bv 64 (a + i)) = false) -> 0 <= v < 2 ^ 64 ->
  LMem.bytes_at AImg0.rsegs m a (LMem.le8 (Z_to_bv 64 v)) ->
  rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v Hv Hr (_ & _ & Hb).
apply (AF0x.val_mem_rdword H m a v Hr). intros k Hk.
assert (Hk' : (k < length (LMem.le8 (Z_to_bv 64 v)))%nat) by (rewrite LMem.length_le8; exact Hk).
rewrite (FFv.decode_mbyte_vis H m (a + Z.of_nat k) (Hv (Z.of_nat k) ltac:(lia))), (Hb k Hk').
pose proof (LB.decode_leafb_le8_byte v k Hk) as E. change (LMem.wa v) with (Z_to_bv 64 v) in E.
destruct (nth_error (LMem.le8 (Z_to_bv 64 v)) k) as [x|] eqn:Ex; [|discriminate E].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. rewrite E.
rewrite AF0x.unsigned_lit_small8; [reflexivity|].
unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* 40 present bytes have some value. *)
Lemma lp_aj : forall (H : word -> bool) (m : word -> option byte) p,
  (forall i, 0 <= i < 40 -> apresent H m (p + i)) ->
  exists aj : list byte, length aj = 40%nat /\
    garr8 tfibsegs (mrestrict H m) p (map (fun x : byte => bv_unsigned x) aj).
Proof.
intros H m p Hp.
destruct (garr8_of_present tfibsegs (mrestrict H m) p 40) as (l & Hl & G).
{ intros a Ha. change (Z.of_nat 40) with 40 in Ha.
  destruct (Hp (a - p) ltac:(lia)) as (Hh & x & Hx).
  replace (p + (a - p)) with a in Hh, Hx by lia.
  exists x. unfold mrestrict. rewrite Hh. exact Hx. }
exists (map (Z_to_bv 8) l). rewrite length_map. split; [exact Hl|].
rewrite map_map.
replace (map (fun x => bv_unsigned (Z_to_bv 8 x)) l) with l; [exact G|].
pose proof (garr8_bytes_ok tfibsegs _ _ _ G) as HB. unfold bytes_ok in HB.
rewrite <- (map_id l) at 1. apply map_ext_in. intros x Hx.
rewrite Forall_forall in HB. symmetry. apply AF0x.unsigned_lit_small8. exact (HB x Hx).
Qed.

(* A byte the view shows is not hidden. *)
Lemma lp_vis : forall (W : world tfibsegs) m a, aview tfibsegs (w_H W) m a <> None -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W m a H. destruct (aview tfibsegs (w_H W) m a) as [v|] eqn:E; [exact (CR.decode_aview_vis W m a v E) | ].
exfalso. exact (H eq_refl).
Qed.

(* Application memory, from amem_range. *)
Lemma lp_app_amem : forall q n, amem_range q n -> 0 <= q -> forall a, q <= a < q + n -> FCells.app_mem a.
Proof.
intros q n Ham H0 a Ha.
assert (C3 : kHighMemBeg = 0x10007fff8000) by reflexivity. assert (C4 : kHighMemEnd = 0x800000000000) by reflexivity.
assert (C5 : kLowMemEnd = 0x7fff8000) by reflexivity.
unfold amem_range in Ham. unfold FCells.app_mem, FCells.LOWMEM_END, FCells.HIGHMEM_BEG, FCells.APPMEM_END.
destruct Ham as [Hm | Hm]; [left | right]; lia.
Qed.

(* A byte off a's 40 bytes is off the leaf's written range. *)
Lemma lp_not_wr : forall (c : bool) p a, ~ (p <= a < p + 40) -> ~ LCK.in_wr (if c then [(p, p + 40)] else []) a.
Proof.
intros c p a Hn HI. unfold LCK.in_wr in HI. destruct c.
- apply Exists_cons in HI. destruct HI as [HI | HI]; [cbn [fst snd] in HI; exact (Hn HI) | inversion HI].
- inversion HI.
Qed.

Lemma lp_saved_bounds : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104.
Proof.
intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section lp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma lp_entry1 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_lp1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_LP)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_lp1.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma lp_entry2 : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_lp2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LP_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_lp2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

Lemma lp_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (PI := PI_transport) (Ereg regs [])).
Proof. intros regs. split; [intros j Hj; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac lp_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "lp_reg: no match for" T; fail
  end.

(* After a run from a state with no region: every byte of the view as before (KD), presence grown (GR). *)
Ltac lp_after HS W KD GR m5 msF :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) => rename mf into msF
  end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

Ltac lp_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

Lemma lp_holds : @onann_lp_stmt fx rc B MT.
Proof.
unfold onann_lp_stmt. intros IGN PF. unfold onann_lp_at.
intros HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (HPCS & HCELLS & HONC & HGU & HGNE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
pose proof HCALL as (_ & LEAF0 & _).
pose proof HFIX as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw & Hfn & Hm &
  HTF & HTFG & HROM & HAP & HRI & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF4096 & HF64 & HFce & HFapp).
pose proof HCUR as ((HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL) & Htw2 & HSH).
pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23) & R20 & R24) & R21 & R22 & R26).
pose proof HDF as (Hcode & Hbuf0 & HBB0 & HSRC & HOFFb & HNGb & Hfp0 & Hfp8 & Hfj & HFB0 & HFAKE & HRDf0 & HOFFf).
destruct (onann_cur_ar B MT LAWS HFIX (proj1 HCUR)) as (HAR0 & HAR2 & Elo & Ehi & Efa & Efl & Hin & EF2 & HFb & HFsh &
  HFG & _ & _ & _ & _ & Hce & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as HCL.
unfold ONANN_FBYTES in HFce, HFapp, HFL.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo0 & Hshi0 & H470 & _).
clear HJi memS.
assert (ES : ESTACK = 4096) by reflexivity.
assert (HSTKn : 4304 <= ONANN_STK) by (cbv; congruence).
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (HOA : ONANN_A = 256) by reflexivity.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. rewrite HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D16. rewrite Hsp16, Z.add_0_r in D16.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *. set (t := spZ regs / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
assert (Hsp1al16 : sp1 mod 16 = 0).
{ destruct Hsp1 as [_ M32]. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite M32, Z.add_0_r in D.
  rewrite D. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring. apply Z.mod_mul. lia. }
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
  rewrite D. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct (lp_body_len b Hcode) as (Hbl0 & Hbl30 & Hlenbb).
assert (HIGN : onann_ign b = negb (DSpec.ann_code (DSpec.fr_cmd b) (Z.of_nat (length (DSpec.fr_body b))) =? 0))
  by (unfold onann_ign, DLib.DIGINET_OK; rewrite Hlenbb; reflexivity).
pose proof HRDf0 as (_ & _ & _ & Hamf & Hfq0 & Hfq63).
assert (Hlenb : 0 < Z.of_nat (length b)) by lia.
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc buf (Z.of_nat (length b)) HAR0 HSRC Hlenb) as HRDb0.
pose proof HRDb0 as (_ & _ & _ & Hamb & Hbq0 & Hbq63).
unfold FRAME_F_SIZE in Hfq63.
(* ---- +0x20c .. +0x214: a0 = fp, a1 = a, `jal diginet_announce_parse` ---- *)
pose proof (lp_entry1 W2 regs2 mem2) as HS.
set (E0 := Eimg (PI := PI_transport) (Ereg regs2 [])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ SHOK LP_B0.
{ lp_awr0. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
lazymatch type of HS with
| st_ok_pi _ _ ?EF _ _ => set (E1 := EF) in HS
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => set (E1 := EF) in HS
end.
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
lp_after HS W2 KD1 GR1 mem2 ms1.
clear HF HFr HG.
lp_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27176)) Q1 ltac:(apply codeptr_val; first [exact HEI | assumption]).
lp_reg HS (Z_to_bv 5 10) (w64 fp) Q10
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact R22).
lp_reg HS (Z_to_bv 5 11) (w64 (F + ONANN_A)) Q11
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact R21).
assert (HP1 : aregs_preserved regs2 (ms_regs ms1)).
{ apply (aregs_preserved_of_st_ok segs (w_H W2) E1 _ ms1 regs2 [] HS).
  - split; [intros j Hj; rewrite E1lo by lia; unfold E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
  - vm_compute. reflexivity. }
assert (Q2 : YK11.getr (ms_regs ms1) (Z_to_bv 5 2) = w64 sp1)
  by exact (eq_trans (HP1 2 ltac:(unfold acallee_saved; lia)) R2).
assert (Q3 : YK11.getr (ms_regs ms1) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans (HP1 3 ltac:(unfold acallee_saved; lia)) (eq_trans R3 Hgp)).
assert (Q4 : YK11.getr (ms_regs ms1) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans (HP1 4 ltac:(unfold acallee_saved; lia)) (eq_trans R4 Htp)).
assert (ESP : bv_unsigned (YK11.getr (ms_regs ms1) (Z_to_bv 5 2)) = sp1)
  by (rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (GSP : spZ (ms_regs ms1) = sp1) by exact ESP.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 ADP.DIGINET_ANNOUNCE_PARSE) mm rom) mdx) Q) end.
clear HS SHOK.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *. clearbody memT regsT. clear ms1.
(* ---- the facts at the call memory ---- *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HART.
assert (KT : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 memT (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 memT
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun _ => False) HAR0 HK).
  - intros a _ _. exact (KD1 a).
  - exact GR1.
  - intros a [].
  - intros b0 m0 i _ _ [].
  - intros a [].
  - intros c p a _ _ []. }
(* f's 64 bytes and b's bytes, kept since the entry *)
assert (HSRCf : trans_src_ok B lyc Sc W memc fp FRAME_F_SIZE) by (right; split; [left; exact HFAKE | exact HRDf0]).
assert (HNGf : forall a, fp <= a < fp + FRAME_F_SIZE -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct HFAKE as (c & p & Hinf & Hf1 & Hf2).
  apply (frm_img segs B LAWS lyc Sc W memc mdc c p a HAR0 Hinf);
    [unfold FRAME_F_SIZE in *; lia | exact (trans_g_img a Hg)]. }
destruct (onann_src_kept B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 memT md1 pos (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b) fp FRAME_F_SIZE HAR0 HART Hfrs Hperm Efa Elo Ehi KT (onann_wr_G Bw b) HNGf HOFFf HSRCf
  ltac:(unfold FRAME_F_SIZE; lia)) as (HSRCfT & KVf).
pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 memT md1 fp FRAME_F_SIZE HART HSRCfT ltac:(unfold FRAME_F_SIZE; lia))
  as HRDfT.
destruct (onann_src_kept B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 memT md1 pos (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b) buf (Z.of_nat (length b)) HAR0 HART Hfrs Hperm Efa Elo Ehi KT (onann_wr_G Bw b) HNGb HOFFb HSRC
  ltac:(lia)) as (HSRCbT & KVb).
pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 memT md1 buf (Z.of_nat (length b)) HART HSRCbT Hlenb) as HRDbT.
pose proof HRDfT as (HVf & HRAf & _ & _ & _ & _).
pose proof HRDbT as (HVb & HRAb & _ & _ & _ & _).
unfold FRAME_F_SIZE in *.
(* the cmd byte, the body and body_len words, the body bytes, at the call memory *)
destruct (lp_f_split _ fp buf b fj Hcode Hfj HFB0) as (G30c & G32c).
assert (G30 : garr8 segs (mrestrict (w_H W2) memT) (fp + 30)
    (map (fun x : byte => bv_unsigned x) [DSpec.b8 (DSpec.fr_cmd b)])).
{ apply (lp_garr8_view (w_H W) (w_H W2) memc memT (fp + 30) _); [|exact G30c].
  intros a Ha. simpl in Ha. apply KVf. lia. }
assert (G32 : garr8 segs (mrestrict (w_H W2) memT) (fp + 32) (map (fun x : byte => bv_unsigned x)
    (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (DSpec.fr_body_len b))))).
{ apply (lp_garr8_view (w_H W) (w_H W2) memc memT (fp + 32) _); [|exact G32c].
  intros a Ha. rewrite length_map, length_app, !LMem.length_le8 in Ha. apply KVf. simpl in Ha. lia. }
assert (Gbb : garr8 segs (mrestrict (w_H W2) memT) (buf + 30) (map (fun x : byte => bv_unsigned x) (DSpec.fr_body b))).
{ apply (lp_garr8_view (w_H W) (w_H W2) memc memT (buf + 30) _); [|exact (lp_body_garr8 _ buf b Hcode HBB0)].
  intros a Ha. rewrite length_map, Hlenbb in Ha. apply KVb. lia. }
assert (Hf30 : LMem.bytes_at AImg0.rsegs memT (fp + 30) [DSpec.b8 (DSpec.fr_cmd b)])
  by exact (LB.decode_leafb_bytes_garr8 W2 memT (fp + 30) _ G30 ltac:(lia) ltac:(cbn; lia)).
assert (Hf32 : LMem.bytes_at AImg0.rsegs memT (fp + 32)
    (LMem.le8 (Z_to_bv 64 (buf + 30)) ++ LMem.le8 (Z_to_bv 64 (Z.of_nat (length (DSpec.fr_body b)))))).
{ rewrite Hlenbb.
  exact (LB.decode_leafb_bytes_garr8 W2 memT (fp + 32) _ G32 ltac:(lia)
    ltac:(rewrite length_app, !LMem.length_le8; cbn; lia)). }
assert (Hbb : LMem.bytes_at AImg0.rsegs memT (buf + 30) (DSpec.fr_body b))
  by exact (LB.decode_leafb_bytes_garr8 W2 memT (buf + 30) _ Gbb ltac:(lia) ltac:(lia)).
(* a's 40 bytes *)
assert (HFbT : forall a, F <= a < F + 1024 -> apresent (w_H W2) memT a) by (intros a Ha; exact (GR1 a (proj1 (HFb a Ha)))).
assert (HVa : forall a, F <= a < F + 1024 -> w_H W2 (Z_to_bv 64 a) = false) by (intros a Ha; exact (proj1 (HFbT a Ha))).
destruct (lp_aj (w_H W2) memT (F + ONANN_A) ltac:(intros i Hi; apply HFbT; lia)) as (aj & Haj & Gaj).
assert (Hajw : LStep.rw_cells AImg0.rsegs memT (F + ONANN_A) [LCells.CB 40 aj]).
{ apply (FFv.decode_rw_of_garr8 (w_H W2) memT (F + ONANN_A) [LCells.CB 40 aj]).
  - cbn [LCells.cells_wf LCells.cell_wf]. split; [exact Haj | exact I].
  - lia.
  - simpl. lia.
  - intros i Hi. simpl in Hi. apply HFbT. lia.
  - cbn [LCells.cells_bytes LCells.cbytes]. rewrite app_nil_r. exact Gaj. }
assert (HSHT : forall i, 32 <= i < 37 -> aview segs (w_H W2) memT (SHADOW_OFF + F / 8 + i) = Some 0)
  by (intros i Hi; rewrite KD1; exact (HSH i Hi)).
assert (HRAa : range_addressable (aview segs (w_H W2) memT) SHADOW_OFF (F + ONANN_A) 40)
  by exact (TransportGNotice.frame_ra_zero _ F (F + ONANN_A) 40 32 37 ltac:(lia) HF8 ltac:(lia) ltac:(lia) HSHT).
(* a apart from f's and the body's ranges *)
assert (HFsep : forall q n, trans_src_ok B lyc Sc W memc q n -> 0 < n -> q + n <= F \/ F + 1024 <= q).
{ intros q n Hs Hn.
  pose proof (trans_src_ok_disj_own B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 ONANN_CID pos q n HAR0 HAR2 Hfrs Hperm
    Efa Hs Hn) as Hd.
  rewrite EF2 in Hd. change (fs_frame_bytes ONANN_CID) with 1024 in Hd. exact Hd. }
pose proof (HFsep fp 64 HSRCf ltac:(lia)) as Hsepf.
pose proof (HFsep buf (Z.of_nat (length b)) HSRC Hlenb) as Hsepb.
unfold amem_range in Hamf, Hamb.
set (cmd := DSpec.fr_cmd b) in *. set (bb := DSpec.fr_body b) in *.
assert (Hok : ADP.ann_ok cmd bb = true -> 33 <= DSpec.fr_body_len b).
{ intros H. unfold ADP.ann_ok in H. apply Z.eqb_eq in H. pose proof (lp_ok_len _ _ H) as H33. lia. }
(* ---- +0x214: diginet_announce_parse ---- *)
eapply SRr_bind.
{ eapply (gx_call_leaf (fx := fx) (rc := rc) (SK := tfib_sink_head) segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 memT md1 (k + 0) _ (YK11.getr regsT 1) _ HJ).
  intros memS HJS.
  eapply (LB.decode_leafb_journal (fx := fx) (SK := tfib_sink_head) B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0
    ((ONANN_CID, pos) :: own) ly2 S2 md1 (k + 0) (sp1 - sp0) ADP.DIGINET_ANNOUNCE_PARSE
    (Some (DSpec.ann_code cmd (Z.of_nat (length bb))))
    (if ADP.ann_ok cmd bb then [(F + ONANN_A, F + ONANN_A + 40)] else [])
    (fun m2 => ADP.ann_ok cmd bb = true -> LStep.rw_cells AImg0.rsegs m2 (F + ONANN_A) (PAnn.ann_cells (buf + 30) bb aj))
    HJS).
  - rewrite GSP. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - exact Q3.
  - exact Q4.
  - intros a Ha. unfold LCK.in_wr in Ha. revert Ha. destruct (ADP.ann_ok cmd bb); intros Ha.
    + apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha]. cbn [fst snd] in Ha.
      right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + inversion Ha.
  - intros HPRE.
    pose proof (LEAF0 fx) as LF.
    unfold transport_leaf_wr_at, LAP.transport_diginet_announce_parse_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT md1 bb aj fp (F + ONANN_A) cmd (buf + 30) (sp1 - 16) HPRE). cbv zeta in LF.
    rewrite ESP in LF. unfold ADP.DIGINET_ANNOUNCE_PARSE_FRAME in LF.
    apply LF; clear LF.
    + exact Q10.
    + exact Q11.
    + lia.
    + lia.
    + exact (DSpec.at8_range b 28).
    + lia.
    + exact Hf30.
    + exact Hf32.
    + exact Hbb.
    + eapply (LB.decode_leafb_stk_journal B); [exact HJS | lia | lia].
    + lia.
    + unfold AKA.off_stk. rewrite ESP. destruct HOFFf as [Ho | Ho]; [left | right]; lia.
    + intros Hk. pose proof (Hok Hk). unfold AKA.off_stk. rewrite ESP. destruct HOFFb as [Ho | Ho]; [left | right]; lia.
    + intros Hk. pose proof (Hok Hk). split; [exact Hajw|]. split; [lia|]. split; [lia|].
      unfold AKA.off_stk. rewrite ESP. left. lia.
    + apply (@LB.decode_leafb_app_stack rc). lia.
    + apply (@LB.decode_leafb_app_stack rc). lia.
    + exact (LB.decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT md1 (proj1 HJS)).
    + unfold AKA.off_stk. rewrite ESP. left. unfold FCells.GOT_CELL_K, FCells.MIDEND. lia.
    + apply (LB.decode_leafb_addressable W2 memT (fp + 30) 1 (fun x Hx => HRAf x ltac:(lia)));
        [lia | lia | unfold FCells.APPMEM_END; lia | intros i Hi; apply (lp_app_amem fp 64 Hamf); lia].
    + intros _. apply (LB.decode_leafb_addressable W2 memT (fp + 40) 8 (fun x Hx => HRAf x ltac:(lia)));
        [lia | lia | unfold FCells.APPMEM_END; lia | intros i Hi; apply (lp_app_amem fp 64 Hamf); lia].
    + intros _. apply (LB.decode_leafb_addressable W2 memT (fp + 32) 8 (fun x Hx => HRAf x ltac:(lia)));
        [lia | lia | unfold FCells.APPMEM_END; lia | intros i Hi; apply (lp_app_amem fp 64 Hamf); lia].
    + intros Hk. pose proof (Hok Hk).
      apply (LB.decode_leafb_addressable W2 memT (buf + 30 + 15) 18 (fun x Hx => HRAb x ltac:(lia)));
        [lia | lia | unfold FCells.APPMEM_END; lia | intros i Hi; apply (lp_app_amem buf _ Hamb); lia].
    + intros _. apply (LB.decode_leafb_addressable W2 memT (F + ONANN_A) 40 HRAa);
        [lia | lia | unfold FCells.APPMEM_END; lia |].
      intros i Hi. replace (F + ONANN_A + i) with (F + (ONANN_A + i)) by lia.
      exact (LB.decode_leafb_app_of_in_app F 1024 (ONANN_A + i) HFapp ltac:(lia)).
    + eapply (LB.decode_leafb_rng_journal B); [exact HJS | lia | lia].
    + exact (proj1 (LB.decode_leafb_rng_cells W2)).
    + exact (proj2 (LB.decode_leafb_rng_cells W2)).
    + apply (LB.decode_leafb_rng W2); [lia | lia | intros a Ha; apply (lp_vis W2 memT a); apply HVf; lia].
    + apply (LB.decode_leafb_rng_shadow W2 memT (fp + 30) 1 (fun x Hx => HRAf x ltac:(lia))); lia.
    + intros _. apply (LB.decode_leafb_rng W2); [lia | lia | intros a Ha; apply (lp_vis W2 memT a); apply HVf; lia].
    + intros _. apply (LB.decode_leafb_rng_shadow W2 memT (fp + 40) 8 (fun x Hx => HRAf x ltac:(lia))); lia.
    + intros _. apply (LB.decode_leafb_rng W2); [lia | lia | intros a Ha; apply (lp_vis W2 memT a); apply HVf; lia].
    + intros _. apply (LB.decode_leafb_rng_shadow W2 memT (fp + 32) 8 (fun x Hx => HRAf x ltac:(lia))); lia.
    + intros Hk. pose proof (Hok Hk).
      apply (LB.decode_leafb_rng W2); [lia | lia | intros a Ha; apply (lp_vis W2 memT a); apply HVb; lia].
    + intros Hk. pose proof (Hok Hk).
      apply (LB.decode_leafb_rng_shadow W2 memT (buf + 30 + 15) 18 (fun x Hx => HRAb x ltac:(lia))); lia.
    + intros _. apply (LB.decode_leafb_rng W2); [lia | lia | intros a Ha; apply HVa; lia].
    + intros _. apply (LB.decode_leafb_rng_shadow W2 memT (F + ONANN_A) 40 HRAa); lia.
    + intros x Hx. revert Hx. destruct (ADP.ann_ok cmd bb); intros Hx; unfold LCK.in_wr in Hx; [|inversion Hx].
      apply Exists_cons in Hx. destruct Hx as [Hx | Hx]; [|inversion Hx]. cbn [fst snd] in Hx.
      split.
      * exact (proj2 (HFb x ltac:(lia))).
      * assert (HxF : frame_addr ly2 ONANN_CID pos <= x < frame_addr ly2 ONANN_CID pos + fs_frame_bytes ONANN_CID)
          by (rewrite EF2; change (fs_frame_bytes ONANN_CID) with 1024; lia).
        exact (proj2 (al_client_img _ _ LAWS _ _ _ _ _ x HART
          (or_intror (or_introl (ex_intro _ ONANN_CID (ex_intro _ pos (conj Hin HxF))))))). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HRES5 & Heff5 & Hgr5 & HX5).
(* ---- what the leaf kept ---- *)
assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - ESTACK <= a < sp1) -> ~ (F + ONANN_A <= a < F + ONANN_A + 40) ->
  aview segs (w_H W2) mem5 a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hw Hap. exact (eq_trans (Heff5 a Ha ltac:(rewrite GSP; exact Hw) (lp_not_wr _ _ a Hap)) (KD1 a)). }
assert (KG5 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem5 (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 memT mem5
    (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b)
    (fun a => (sp1 - ESTACK <= a < sp1) \/ LCK.in_wr (if ADP.ann_ok cmd bb then [(F + ONANN_A, F + ONANN_A + 40)] else []) a)
    HGX HAR0 HAR2 Hfrs Hbl HlyF EF eq_refl FFL); [lia | lia | | exact KT | | exact Hgr5].
  - intros a [Ha | Ha]; [left; lia|]. right; left.
    unfold LCK.in_wr in Ha. revert Ha. destruct (ADP.ann_ok cmd bb); intros Ha; [|inversion Ha].
    apply Exists_cons in Ha. destruct Ha as [Ha | Ha]; [|inversion Ha]. cbn [fst snd] in Ha.
    unfold dkg_nf. left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - intros a Ha Hn. apply (Heff5 a Ha).
    + intros H'. apply Hn. left. rewrite <- GSP. exact H'.
    + intros H'. apply Hn. right. exact H'. }
pose proof (HRES5 _ eq_refl) as X10.
assert (HP5' : aregs_preserved regs2 regs5) by exact (aregs_preserved_trans _ _ _ HP1 HP5).
(* the facts both cuts carry, from mem5 to the cut's memory *)
assert (HSVK : forall m', (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) mem5 a) ->
  Forall (fun o : Z * Z => rdword (aview segs (w_H W2) m') (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ intros m' KD'. rewrite Forall_forall in HSV |- *. intros o Ho. pose proof (lp_saved_bounds o Ho) as Hob.
  rewrite <- (HSV o Ho). apply rdword_ext. intros i Hi. rewrite KD'. apply KL; lia. }
assert (HFLK : forall m', (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) mem5 a) ->
  rdword (aview segs (w_H W2) m') (F + 1024 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ intros m' KD'. rewrite <- HFL. apply rdword_ext. intros i Hi. rewrite KD'. apply KL; lia. }
assert (HTWK : forall m', (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) mem5 a) ->
  tw_at TMAP_A (aview segs (w_H W2) m') Bw).
{ intros m' KD'. apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw2|].
  intros x Hx. pose proof Hx as (o & b0 & n0 & Hin' & Hx').
  assert (HxG : inG TG.G_HARNESS x).
  { unfold inG. apply Exists_exists. exists (b0, n0).
    split; [exact (TMAP_A_in_G o b0 n0 Hin') | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_G_HARNESS_hull x HxG) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  rewrite KD'. apply KL; [lia | lia |].
  intros Hxa. exact (HFG x ltac:(lia) HxG). }
assert (KGK : forall m', (forall a, aview segs (w_H W2) m' a = aview segs (w_H W2) mem5 a) ->
  (forall a, apresent (w_H W2) mem5 a -> apresent (w_H W2) m' a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 m' (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
{ intros m' KD' GR'.
  apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem5 m'
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun _ => False) HAR0 KG5).
  - intros a _ _. exact (KD' a).
  - exact GR'.
  - intros a [].
  - intros b0 m0 i _ _ [].
  - intros a [].
  - intros c p a _ _ []. }
(* ---- +0x218: `beqz a0`, from a state with no region ---- *)
rewrite Q1.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + LP_C2)) mm rom) mdx) Q) end.
pose proof (lp_entry2 W2 regs5 mem5) as HS.
set (Eb := Eimg (PI := PI_transport) (Ereg regs5 [])) in HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) Eb (mrestrict (w_H W2) mem5)) by constructor.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eb n = YK11.getr regs5 r)
  by (intros n r Hn; unfold Eb; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D10 : sv_denot Eb (SOff 10 0) = Z_to_bv 64 (DSpec.ann_code cmd (Z.of_nat (length bb))))
  by (cbn [sv_denot]; rewrite (EEb 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
psrr_branch_tok RUN BR HS SHOK LP_B0.
- (* code 0: to the personality cut +0x248 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot Eb (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (lp_eqb0 _ (lp_code_range _ _)) in Hc. apply Z.eqb_eq in Hc.
  assert (Hokt : ADP.ann_ok cmd bb = true) by (unfold ADP.ann_ok; rewrite Hc; reflexivity).
  paj_run_to_tok RUNTO HS HJ5 SHOK LP_B0 ONANN_PF.
  { lp_awr0. }
  lp_after HS W2 KD3 GR3 mem5 msF.
  assert (HPF : aregs_preserved regs2 (ms_regs msF)).
  { apply (aregs_preserved_trans _ _ _ HP5').
    apply (aregs_preserved_of_st_ok segs (w_H W2) _ _ msF regs5 [] HS).
    - split; [intros j Hj; rewrite ?ew_ewset_other by lia; unfold Eb; apply Eimg_low; unfold A_TEXT; lia
             | reflexivity].
    - vm_compute. reflexivity. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PF)) mm rom) mdx) Q) end.
  apply (PF HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_pf_cur.
    refine (conj (conj HJ5 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO
      (conj (KGK _ KD3 GR3) (conj (HSVK _ KD3) (HFLK _ KD3))))))))) (conj (HTWK _ KD3) (conj _ _))).
    * rewrite HIGN, Hc. reflexivity.
    * destruct (HX5 Hokt) as ((Hwf & Hb) & _).
      unfold PAnn.ann_cells in Hwf, Hb. cbn [LCells.cells_wf LCells.cell_wf] in Hwf.
      destruct Hwf as (L1 & L2 & L3 & _).
      cbn [LCells.cells_bytes LCells.cbytes] in Hb.
      apply LMem.bytes_at_app in Hb. destruct Hb as [HbV Hb]. rewrite L1 in Hb.
      apply LMem.bytes_at_app in Hb. destruct Hb as [HbN Hb]. rewrite L2 in Hb.
      apply LMem.bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite L3 in Hb.
      apply LMem.bytes_at_app in Hb. destruct Hb as [Hb24 Hb]. rewrite LMem.length_le8 in Hb.
      apply LMem.bytes_at_app in Hb. destruct Hb as [Hb32 _].
      change (Z.of_nat 10) with 10 in HbN, Hb24, Hb32. change (Z.of_nat 4) with 4 in Hb24, Hb32.
      change (Z.of_nat 8) with 8 in Hb32.
      unfold DSpec.ann_version in HbV. rewrite lp_field_prefix in HbV.
      apply LMem.bytes_at_app in HbV. destruct HbV as [HbV _].
      unfold DSpec.ann_name in HbN. rewrite lp_field_prefix in HbN.
      apply LMem.bytes_at_app in HbN. destruct HbN as [HbN _].
      pose proof (lp_ann_field_len (skipn 15 bb)) as LV. pose proof (lp_ann_field_len (skipn 24 bb)) as LN.
      unfold onann_a_ok. fold bb.
      refine (conj _ (conj _ (conj _ (conj _ _)))).
      -- apply (lp_garr8_view (w_H W2) (w_H W2) mem5 (ms_mem msF) (F + ONANN_A) _).
         { intros a Ha. exact (KD3 a). }
         apply (FFv.decode_bytes_garr8 (w_H W2) mem5 (F + ONANN_A)); [|exact HbV].
         intros j Hj. apply HVa. lia.
      -- apply (lp_garr8_view (w_H W2) (w_H W2) mem5 (ms_mem msF) (F + ONANN_A + 10) _).
         { intros a Ha. exact (KD3 a). }
         apply (FFv.decode_bytes_garr8 (w_H W2) mem5 (F + ONANN_A + 10)); [|exact HbN].
         intros j Hj. apply HVa. lia.
      -- rewrite (rdword_ext _ _ _ (fun k0 _ => KD3 _)).
         apply (lp_rdword_le8 (w_H W2) mem5 (F + ONANN_A + 24) (buf + 30)).
         ++ intros i Hi. apply HVa. lia.
         ++ lia.
         ++ replace (F + ONANN_A + 24) with (F + ONANN_A + 10 + 10 + 4) by lia. exact Hb24.
      -- rewrite (rdword_ext _ _ _ (fun k0 _ => KD3 _)).
         apply (lp_rdword_le8 (w_H W2) mem5 (F + ONANN_A + 32) 15).
         ++ intros i Hi. apply HVa. lia.
         ++ lia.
         ++ replace (F + ONANN_A + 32) with (F + ONANN_A + 10 + 10 + 4 + 8) by lia. exact Hb32.
      -- intros i Hi. rewrite KD3. rewrite KL; [exact (HSH i Hi) | | |].
         ++ pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
            assert (F / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
            change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF. lia.
         ++ pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
            assert (F / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
            change (2 ^ 47 / 8) with (2 ^ 44) in *. unfold SHADOW_OFF. lia.
         ++ intros [Hx1 Hx2]. rewrite HOA in Hx1, Hx2.
            pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8p.
            pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8m.
            unfold SHADOW_OFF in Hx1, Hx2.
            destruct HFapp as (_ & [HL | [HH _]]).
            ** unfold YG0f.kLowShadowBeg in HL.
               clear - HL Hx2 HF8p Hi. lia.
            ** unfold YG0f.kHighMemBeg in HH.
               clear - HH Hx1 HF8m Hi. lia.
  + unfold onann_regs_pf, onann_regs_ign, onann_regs_rel, onann_regs_base.
    refine (conj (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) _) (conj _ _)) (conj _ (conj _ _))).
    * exact (eq_trans (HPF 2 ltac:(unfold acallee_saved; lia)) R2).
    * exact (eq_trans (HPF 3 ltac:(unfold acallee_saved; lia)) R3).
    * exact (eq_trans (HPF 4 ltac:(unfold acallee_saved; lia)) R4).
    * exact (eq_trans (HPF 8 ltac:(unfold acallee_saved; lia)) R8).
    * exact (eq_trans (HPF 9 ltac:(unfold acallee_saved; lia)) R9).
    * exact (eq_trans (HPF 18 ltac:(unfold acallee_saved; lia)) R18).
    * exact (eq_trans (HPF 19 ltac:(unfold acallee_saved; lia)) R19).
    * exact (eq_trans (HPF 23 ltac:(unfold acallee_saved; lia)) R23).
    * exact (eq_trans (HPF 20 ltac:(unfold acallee_saved; lia)) R20).
    * exact (eq_trans (HPF 24 ltac:(unfold acallee_saved; lia)) R24).
    * exact (eq_trans (HPF 21 ltac:(unfold acallee_saved; lia)) R21).
    * exact (eq_trans (HPF 22 ltac:(unfold acallee_saved; lia)) R22).
    * exact (eq_trans (HPF 26 ltac:(unfold acallee_saved; lia)) R26).
- (* code <> 0: to the ignore cut +0x21c *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot Eb (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (lp_eqb0 _ (lp_code_range _ _)) in Hc.
  paj_run_to_tok RUNTO HS HJ5 SHOK LP_B0 ONANN_IGN.
  { lp_awr0. }
  lp_after HS W2 KD3 GR3 mem5 msF.
  assert (HPF : aregs_preserved regs2 (ms_regs msF)).
  { apply (aregs_preserved_trans _ _ _ HP5').
    apply (aregs_preserved_of_st_ok segs (w_H W2) _ _ msF regs5 [] HS).
    - split; [intros j Hj; rewrite ?ew_ewset_other by lia; unfold Eb; apply Eimg_low; unfold A_TEXT; lia
             | reflexivity].
    - vm_compute. reflexivity. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_IGN)) mm rom) mdx) Q) end.
  apply (IGN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_ign_cur.
    refine (conj (conj HJ5 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO
      (conj (KGK _ KD3 GR3) (conj (HSVK _ KD3) (HFLK _ KD3))))))))) (conj (HTWK _ KD3) _)).
    rewrite HIGN, Hc. reflexivity.
  + unfold onann_regs_ign, onann_regs_rel, onann_regs_base.
    refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) _) (conj _ _)).
    * exact (eq_trans (HPF 2 ltac:(unfold acallee_saved; lia)) R2).
    * exact (eq_trans (HPF 3 ltac:(unfold acallee_saved; lia)) R3).
    * exact (eq_trans (HPF 4 ltac:(unfold acallee_saved; lia)) R4).
    * exact (eq_trans (HPF 8 ltac:(unfold acallee_saved; lia)) R8).
    * exact (eq_trans (HPF 9 ltac:(unfold acallee_saved; lia)) R9).
    * exact (eq_trans (HPF 18 ltac:(unfold acallee_saved; lia)) R18).
    * exact (eq_trans (HPF 19 ltac:(unfold acallee_saved; lia)) R19).
    * exact (eq_trans (HPF 23 ltac:(unfold acallee_saved; lia)) R23).
    * exact (eq_trans (HPF 20 ltac:(unfold acallee_saved; lia)) R20).
    * exact (eq_trans (HPF 24 ltac:(unfold acallee_saved; lia)) R24).
Qed.
End lp.

(* The parse piece of the walk of on_announce (OnannCut.v onann_lp_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem onann_piece_lp : forall fx rc B MT, @onann_lp_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@lp_holds fx rc B MT). Qed.
