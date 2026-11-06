(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YI08 YN3v YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI5w YI5z.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YO07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO08 YI0f YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Export YC7y YC7z.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Definition xcgif_vals (path hw pf : Z) (s : cgif_st) : list Z :=
[ frame_ptr (nth 0 (cg_frames s) None); frame_ptr (nth 1 (cg_frames s) None); frame_ptr (nth 2 (cg_frames s) None);
cg_pal s; path; cg_attr s; cg_gen s; cg_W s; cg_H s; cg_ngp s; cg_loops s;
hw  ; 0  ; cg_raw s; pf  ; cg_cur s; cg_ihead s ].
Definition xcgif_at (wfn path hw pf : Z) (m : word -> option byte) (g : Z) (s : cgif_st) : Prop :=
obj_at segs m g LAY_CGIF (xcgif_vals path hw pf s) /\
obj_at segs m (cg_raw s) LAY_Raw (traw_vals wfn g s) /\
(forall f, In (Some f) (cg_frames s) -> obj_at segs m (fr_ptr f) LAY_Frame (frame_vals f)).
Lemma tcgif_at_x : forall wfn hw m g s, tcgif_at segs wfn hw m g s = xcgif_at wfn 0 hw 0 m g s.
Proof. reflexivity. Qed.
Definition gcfg_of (s : cgif_st) (GPAL : list Z) : YO07.gcfg :=
YO07.mkG (cg_W s) (cg_H s) (cg_attr s) (cg_gen s) (cg_ngp s) GPAL.
Definition frame_relbA (wg : bool) (m : word -> option byte) (N : Z) (f : frame_st) (fr : YO07.frame) : Prop :=
fr_attr f = YO07.f_attr fr /\ (if wg then fr_gen f = YO07.f_gen fr else True) /\ fr_delay f = YO07.f_delay fr /\
fr_nlp f = YO07.f_nlp fr /\ (Z.land (fr_attr f) 6 <> 0 -> fr_ctidx f = YO07.f_ctrans fr) /\ fr_disp f = YO07.f_disp fr /\
fr_tidx f = YO07.f_trans fr /\
garr8 segs m (fr_img f) (YO07.f_img fr) /\ Z.of_nat (length (YO07.f_img fr)) = N /\
(Z.land (fr_attr f) 1 <> 0 -> garr8 segs m (fr_lpal f) (YO07.f_lpal fr) /\ Z.of_nat (length (YO07.f_lpal fr)) = 3 * fr_nlp f).
Definition oframe_relbA (wg : bool) (m : word -> option byte) (N : Z) (o : option frame_st) (q : option YO07.frame) : Prop :=
match o, q with
| None, None => True
| Some f, Some fr => frame_relbA wg m N f fr
| _, _ => False
end.
Definition cgif_live (gs : YO07.gif_st) : Prop := YO07.s_cur gs = YO07.C_OK \/ YO07.s_cur gs = YO07.C_PENDING.
Definition cgif_occ (s : cgif_st) (gs : YO07.gif_st) : Prop :=
(nth 0 (cg_frames s) None = None <-> YO07.s_q0 gs = None) /\
(nth 1 (cg_frames s) None = None <-> YO07.s_q1 gs = None) /\
(nth 2 (cg_frames s) None = None <-> YO07.s_q2 gs = None).
Section d.
Variable K : asink_syms.
Definition cgif_relA (m : word -> option byte) (md : Model) (s : cgif_st) (f : Z) (N : Z) (GPAL : list Z) (gs : YO07.gif_st) : Prop :=
(rc_int (cg_cur s) = YO07.s_cur gs /\ cgif_occ s gs) /\
asink_at segs K m md f (concat (YO07.s_out gs)) /\
(cgif_live gs ->
rc_int (rw_cur s) = YO07.s_rcur gs /\ rw_attr s = raw_attr_of (cg_attr s) /\ cg_ihead s = YO07.s_ihead gs /\
(Z.land (cg_attr s) 4 = 0 -> garr8 segs m (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) /\
oframe_relbA false m N (nth 0 (cg_frames s) None) (YO07.s_q0 gs) /\
oframe_relbA true m N (nth 1 (cg_frames s) None) (YO07.s_q1 gs) /\
oframe_relbA true m N (nth 2 (cg_frames s) None) (YO07.s_q2 gs)).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition trawnew_specX (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg : Z) rest (Sg GCT : list Z),
afn_pre segs B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 8 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj segs B ly S W mem cfgp 40 ->
obj_at segs (rdW W mem) cfgp LAY_RawConfig [wfn; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: rest) ->
val_mem segs (rdW W mem) (g + 56) 8 hw ->
val_mem segs (rdW W mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (rdW W mem) (g + 80) 8 pf -> pf <> 0 ->
asink_at segs K (rdW W mem) md pf Sg -> Z.of_nat (length Sg) + HDR_OUT <= SINK_MAX ->
(sgct <> 0 -> In (pga, Npg) rest /\ Z_to_bv 64 pga = Z_to_bv 64 pgct /\ 3 * sgct <= Npg /\
garr8 segs (rdW W mem) pga GCT /\ 3 * sgct <= Z.of_nat (length GCT)) ->
st_nev S + EV_RAWNEW <= EV_MAX -> blocks_bytes S + 2 ^ 16 <= LIVE_MAX ->
mo_ok MT S (mo_malloc MT RAW_SIZE) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TRAWNEW_STK (asink_fp pf) regs ly S W mem md EV_RAWNEW
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
mo_le MT S S' (mo_malloc MT RAW_SIZE) /\
((res = 0 /\ 256 < sgct /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
asink_at segs K (rdW W' mem') md' pf Sg) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly' S') ((res, RAW_SIZE) :: ablocks B ly S) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs) (asink_fp pf) (ablocks B ly S) blc ly' [] (res + i)) /\
aftok (asink_fp pf) (ablocks B ly S) (res, RAW_SIZE) /\
obj_at segs (rdW W' mem') res LAY_Raw [wfn; g; pgct; rattr; Wd; Hd; sgct; loops; R_PENDING] /\
asink_at segs K (rdW W' mem') md' pf (Sg ++ YO07.raw_header Wd Hd sgct GCT rattr loops))))).
Definition trawadd_specX (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch
(raw g cfp : Z) (gct rattr Wd Hd sgct loops rcur ctx pf : Z) (path hw : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)) (Sg IMG LCT : list Z),
afn_pre segs B TRAWADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 8 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 raw -> getr regs 11 = w64 cfp ->
afobj segs B ly S W mem cfp 40 ->
obj_at segs (rdW W mem) cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at segs (rdW W mem) raw LAY_Raw [wfn; g; gct; rattr; Wd; Hd; sgct; loops; rcur] ->
sgct <= 256 ->
val_mem segs (rdW W mem) (g + 56) 8 hw -> 0 <= hw < 2 ^ 64 ->
val_mem segs (rdW W mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (rdW W mem) (g + 80) 8 pf -> pf <> 0 ->
asink_at segs K (rdW W mem) md pf Sg -> Z.of_nat (length Sg) + FRAME_OUT (w * h) <= SINK_MAX ->
1 <= w -> 1 <= h -> w * h <= 100000000 -> w * h <= Nimg ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: (pf, FILE_BLOCK) :: rest) ->
(0 < slct <= 256 -> exists Nl rest', Permutation rest ((lct, Nl) :: rest') /\ 3 * slct <= Nl /\
garr8 segs (rdW W mem) lct LCT /\ 3 * slct <= Z.of_nat (length LCT)) ->
garr8 segs (rdW W mem) img IMG -> Z.of_nat (length IMG) = w * h ->
st_nev S + EV_RAWADD <= EV_MAX -> blocks_bytes S + LIVE_RAWADD <= LIVE_MAX ->
mo_ok MT S (xm_rawadd XN (w * h)) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TRAWADD_STK ((raw + 40, raw + 44) :: asink_fp pf) regs ly S W mem md EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at segs (rdW W' mem') raw LAY_Raw [wfn; g; gct; rattr; Wd; Hd; sgct; loops; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(exists code bytes,
YO07.raw_addframe (YO07.flag rattr 1) sgct (rc_int rcur) IMG fattr w h top left delay slct LCT disp tidx = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32 /\
asink_at segs K (rdW W' mem') md' pf (Sg ++ bytes) /\
Z.of_nat (length bytes) <= FRAME_OUT (w * h)) /\
mo_le MT S S' (xn_rawadd XN (w * h)))).
Definition tflush_specX (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (i : nat) (fr : frame_st) (f : Z) (path hw : Z)
(rest : list (Z * Z)) (Sg GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame),
afn_pre segs B TFLUSH_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g ->
xcgif_at wfn path hw f (rdW W mem) g s -> cgif_wf s N -> f <> 0 ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some fr) ->
getr regs 11 = w64 (fr_ptr fr) ->
getr regs 12 = w64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rest) ->
asink_at segs K (rdW W mem) md f Sg -> Z.of_nat (length Sg) + FRAME_OUT N <= SINK_MAX ->
(Z.land (cg_attr s) 4 = 0 -> garr8 segs (rdW W mem) (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) ->
frame_relbA true (rdW W mem) N fr cur -> oframe_relbA false (rdW W mem) N (nth (i - 1) (cg_frames s) None) bef ->
rw_attr s = raw_attr_of (cg_attr s) ->
st_nev S + EV_FLUSH <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
mo_ok MT S (xm_flush XN N) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base segs B TFLUSH_STK ((fr_ptr fr + 20, fr_ptr fr + 24) :: (cg_raw s + 40, cg_raw s + 44) :: asink_fp f)
regs ly S W mem md EV_FLUSH
(fun ly' S' W' regs' mem' md' => exists r rwcur' : Z,
getr regs' 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
xcgif_at wfn path hw f (rdW W' mem') g (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') /\
cgif_wf (flush_upd s i (fl_gen3 (gcfg_of s GPAL) cur bef) rwcur') N /\
Permutation (ablocks B ly' S') (cgif_blocks g s N ++ (f, FILE_BLOCK) :: rest) /\
(exists code bytes,
YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
asink_at segs K (rdW W' mem') md' f (Sg ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
mo_le MT S S' (xn_flush XN N))).
End e.
End d.
End c.
End b.
