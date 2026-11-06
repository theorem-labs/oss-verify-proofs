(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC20.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI5w YI5z.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition WCB_STK : Z := 16.
Definition CGIF_OBJ : Z := 96.
Definition LZW_TSTK : Z := 336 + ASTACK.
Definition LZW_EV : Z := 19.
Definition TRAWCLOSE_STK : Z := 32 + ASTACK.
Definition TRAWNEW_STK : Z := 192 + ASTACK.
Definition TRAWADD_STK : Z := 320 + LZW_TSTK.
Definition TFLUSH_STK : Z := 400 + TRAWADD_STK.
Definition TCLOSE_STK : Z := 80 + TFLUSH_STK.
Definition TADDFRAME_STK : Z := 224 + TFLUSH_STK.
Definition TNEWGIF_STK : Z := 192 + TRAWNEW_STK.
Definition TRFC_STK : Z := 112 + ASTACK.
Definition EV_RAWCLOSE : Z := 1.
Definition EV_RAWNEW : Z := 4.
Definition EV_RAWADD : Z := 8 + LZW_EV.
Definition EV_FLUSH : Z := 8 + EV_RAWADD.
Definition EV_CLOSE : Z := 16 + 2 * EV_FLUSH.
Definition EV_ADDFRAME : Z := 12 + EV_FLUSH.
Definition EV_NEWGIF : Z := 8 + EV_RAWNEW.
Definition EV_RFC : Z := 6.
Definition LIVE_RAWADD : Z := 2 ^ 30.
Definition LIVE_FLUSH : Z := 2 ^ 30 + 2 ^ 28.
Definition LIVE_ADDFRAME : Z := 2 ^ 31.
Definition LIVE_NEWGIF : Z := 2 ^ 20.
Definition LIVE_RFC : Z := 2 ^ 28.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Variable segs : list Segment.
Definition tcgif_vals (hw : Z) (s : cgif_st) : list Z :=
[ frame_ptr (nth 0 (cg_frames s) None); frame_ptr (nth 1 (cg_frames s) None); frame_ptr (nth 2 (cg_frames s) None);
cg_pal s; 0  ; cg_attr s; cg_gen s; cg_W s; cg_H s; cg_ngp s; cg_loops s;
hw  ; 0  ; cg_raw s; 0  ; cg_cur s; cg_ihead s ].
Definition traw_vals (wfn : Z) (g : Z) (s : cgif_st) : list Z :=
[ wfn; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rw_cur s ].
Definition tcgif_at (wfn hw : Z) (m : word -> option byte) (g : Z) (s : cgif_st) : Prop :=
obj_at segs m g LAY_CGIF (tcgif_vals hw s) /\
obj_at segs m (cg_raw s) LAY_Raw (traw_vals wfn g s) /\
(forall f, In (Some f) (cg_frames s) -> obj_at segs m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition afobj (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
p mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
Definition apost_base (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Section o.
Variable B : asyms.
Definition hwcb_spec (hw : Z) : Prop :=
0 <= hw < 2 ^ 64 /\ hw mod 2 = 0 /\
forall (W : world segs) (regs : bvmap 5 word) mem md (Q : world segs -> config -> Prop),
(forall mat' regs', aregs_preserved regs regs' -> getr regs' 10 = w64 0 -> getr regs' 1 = getr regs 1 ->
Q W (mkCfg (mkst regs' (v_jalr (getr regs 1) 0) mem (seg_rom segs)) (with_vm_backing (m_vm_lazy md) mat' md))) ->
SRr segs W (mkCfg (mkst regs (Z_to_bv 64 hw) mem (seg_rom segs)) md) Q.
Definition wcb_post (regs : bvmap 5 word) ly S W mem md : world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B WCB_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S).
Definition twcb_spec (wfn hw : Z) : Prop :=
forall W ly S regs mem md ch g ctx,
afn_pre segs B WCB_STK ly S W regs mem md ch ->
getr regs 10 = w64 g ->
In (g, CGIF_OBJ) (ablocks B ly S) ->
val_mem segs (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem segs (mrestrict (w_H W) mem) (g + 64) 8 ctx ->
val_mem segs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
0 <= ctx < 2 ^ 64 ->
SRr segs W (cfg_at segs wfn regs mem md) (wcb_post regs ly S W mem md).
Definition trawclose_spec (a : Z) (rctrace : list Z) (wfn hw : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (raw g rcur ctx : Z) rest,
afn_pre segs B TRAWCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 raw ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
val_mem segs (mrestrict (w_H W) mem) raw 8 wfn ->
val_mem segs (mrestrict (w_H W) mem) (raw + 8) 8 g ->
val_mem segs (mrestrict (w_H W) mem) (raw + 40) 4 rcur -> 0 <= rcur < 2 ^ 32 ->
val_mem segs (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem segs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_nev S + EV_RAWCLOSE <= EV_MAX ->
In rctrace (as_universe B) ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TRAWCLOSE_STK (ablocks_fp [(raw, RAW_SIZE)]) regs ly S W mem md EV_RAWCLOSE
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') ((g, CGIF_SIZE) :: rest))).
Definition trawnew_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx : Z) rest,
afn_pre segs B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 8 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp 40 ->
obj_at segs (mrestrict (w_H W) mem) cfgp LAY_RawConfig [wfn; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
val_mem segs (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem segs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_nev S + EV_RAWNEW <= EV_MAX -> blocks_bytes S + 2 ^ 16 <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TRAWNEW_STK [] regs ly S W mem md EV_RAWNEW
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly' S') ((res, RAW_SIZE) :: ablocks B ly S) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (res + i)) /\
aftok [] (ablocks B ly S) (res, RAW_SIZE) /\
obj_at segs (mrestrict (w_H W') mem') res LAY_Raw [wfn; g; pgct; rattr; Wd; Hd; sgct; loops; R_PENDING])))).
Definition trawadd_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch
(raw g cfp : Z) (gct rattr Wd Hd sgct loops rcur ctx : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)),
afn_pre segs B TRAWADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 8 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 raw -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 40 ->
obj_at segs (mrestrict (w_H W) mem) cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at segs (mrestrict (w_H W) mem) raw LAY_Raw [wfn; g; gct; rattr; Wd; Hd; sgct; loops; rcur] ->
sgct <= 256 ->
val_mem segs (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem segs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem segs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
1 <= w -> 1 <= h -> w * h <= 100000000 -> w * h <= Nimg ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
(0 < slct <= 256 -> exists Nl rest', Permutation rest ((lct, Nl) :: rest') /\ 3 * slct <= Nl) ->
st_nev S + EV_RAWADD <= EV_MAX -> blocks_bytes S + LIVE_RAWADD <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TRAWADD_STK [(raw + 40, raw + 44)] regs ly S W mem md EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at segs (mrestrict (w_H W') mem') raw LAY_Raw [wfn; g; gct; rattr; Wd; Hd; sgct; loops; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B ly S))).
Definition tflush_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (i : nat) (f : frame_st) (rest : list (Z * Z)),
afn_pre segs B TFLUSH_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g ->
tcgif_at wfn hw (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = w64 (fr_ptr f) ->
getr regs 12 = w64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_nev S + EV_FLUSH <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TFLUSH_STK [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] regs ly S W mem md EV_FLUSH
(fun ly' S' W' regs' mem' md' => exists r gen' rwcur' : Z,
getr regs' 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
tcgif_at wfn hw (mrestrict (w_H W') mem') g (flush_upd s i gen' rwcur') /\ cgif_wf (flush_upd s i gen' rwcur') N /\
Permutation (ablocks B ly' S') (cgif_blocks g s N ++ rest))).
Definition tclose_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)),
afn_pre segs B TCLOSE_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g ->
tcgif_at wfn hw (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_nev S + EV_CLOSE <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TCLOSE_STK (ablocks_fp (cgif_blocks g s N)) regs ly S W mem md EV_CLOSE
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest)).
Definition tnewgif_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops : Z) (rest : list (Z * Z)),
afn_pre segs B TNEWGIF_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp 48 ->
obj_at segs (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; 0; attr; gen; Wd; Hd; ngp; loops; hw; 0] ->
Wd * Hd <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
st_nev S + EV_NEWGIF <= EV_MAX -> blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TNEWGIF_STK [] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ exists s,
tcgif_at wfn hw (mrestrict (w_H W') mem') res s /\ cgif_wf s (Wd * Hd) /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (ablocks B ly' S') (cgif_blocks res s (Wd * Hd) ++ ablocks B ly S) /\
(forall b, In b (cgif_blocks res s (Wd * Hd)) ->
aftok [] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (fst b + i)))))).
Definition taddframe_spec (a : Z) (CTX : list (list Z)) (wfn hw rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)),
afn_pre segs B TADDFRAME_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 32 ->
obj_at segs (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
tcgif_at wfn hw (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (ablocks B ly S)
(cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
st_nev S + EV_ADDFRAME <= EV_MAX -> blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs mem md)
(apost_base B TADDFRAME_STK (ablocks_fp (cgif_blocks g s N)) regs ly S W mem md EV_ADDFRAME
(fun ly' S' W' regs' mem' md' => exists s' : cgif_st,
tcgif_at wfn hw (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (ablocks B ly' S')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) blc ly' [] (fst b + i)))).
Definition trfc_spec (a : Z) (CTX : list (list Z)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur : Z) (cid pos : Z) ch,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall b, In b (ablocks B ly S) -> In b Bb) -> Permutation (ablocks B lyc Sc) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 st -> getr regs 11 = w64 dst -> getr regs 12 = w64 N ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= dst -> dst + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid -> dst mod 8 = 0 ->
spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF st 24 ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF dst 32 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
val_mem segs (mrestrict (w_H W) memc) st 8 pdata -> val_mem segs (mrestrict (w_H W) memc) (st + 8) 8 nb ->
val_mem segs (mrestrict (w_H W) memc) (st + 16) 8 cur ->
st_nev S + k + EV_RFC <= EV_MAX -> blocks_bytes Sc + LIVE_RFC <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res cur2 : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_RFC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
getr regs2 10 = w64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - TRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
val_mem segs (mrestrict (w_H W2) mem2) st 8 pdata /\ val_mem segs (mrestrict (w_H W2) mem2) (st + 8) 8 nb /\
val_mem segs (mrestrict (w_H W2) mem2) (st + 16) 8 cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ exists leak, Permutation (ablocks B ly2 S2) (leak ++ Bb) /\
(leak = [] \/ exists lpa nlp, leak = [(lpa, 3 * nlp)] /\ 0 <= nlp < 2 ^ 16) /\
(forall b, In b leak -> aftok FP (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (fst b + i))) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx,
obj_at segs (mrestrict (w_H W2) mem2) dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (ablocks B ly2 S2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
(forall b, In b ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ->
aftok FP (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (fst b + i))))).
Definition tlzw_kept (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte)
(W2 : world segs) (mem2 : word -> option byte) (sp pR : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_TSTK <= a < sp) -> ~ (pR <= a < pR + 12) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview segs (w_H W2) mem2 (b + i) = aview segs (w_H W) memc (b + i)) /\
(forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ (pR <= a < pR + 12) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - LZW_TSTK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - LZW_TSTK <= a < sp -> apresent (w_H W2) mem2 a).
Definition tlzw_pR_ok (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (pR : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames Sc) /\ (forall a, pR <= a < pR + 16 -> in_zr a (frame_rng lyc (cid, pos))) /\
aview segs (w_H W) memc (shadow_addr pR) = Some 0 /\ aview segs (w_H W) memc (shadow_addr pR + 1) = Some 0)
\/ (ly_stk_lo lyc <= pR /\ pR + 16 <= ly_stk_hi lyc).
Definition tlzw_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (pR : Z) : world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + LZW_EV) /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
((res = 0 /\
exists bb Lbb M,
Permutation (ablocks B ly2 S2) ((bb, Lbb) :: ablocks B lyc Sc) /\ 4096 <= bb /\ 1 <= M <= Lbb /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (bb + i)) /\
aftok FP (ablocks B ly S) (bb, Lbb) /\
val_mem segs (mrestrict (w_H W2) mem2) pR 8 bb /\ val_mem segs (mrestrict (w_H W2) mem2) (pR + 8) 4 M /\
tlzw_kept lyc Sc W memc W2 mem2 (spZ regs) pR (fun a => bb <= a < bb + req_size Lbb))
\/ ((res = 2 \/ res = 5) /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
tlzw_kept lyc Sc W memc W2 mem2 (spZ regs) pR (fun _ => False) /\
(forall a, pR <= a < pR + 12 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a))).
Definition tlzw_spec (a : Z) (CTX : list (list Z)) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) ch,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img ->
getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
(forall a, pR <= a < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a) ->
tlzw_pR_ok lyc Sc W memc pR ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
SRr segs W (cfg_at segs a regs memc mdc)
(tlzw_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR).
End o.
End l.
End j.
