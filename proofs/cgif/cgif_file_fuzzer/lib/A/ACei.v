(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YP09 YI04 YI09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l ACej ACeh ACek ACeq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_cgif_raw_close : Z := 0x86684.
Definition A_cgif_raw_newgif : Z := 0x84178.
Definition A_cgif_raw_addframe : Z := 0x84894.
Definition A_flushFrame : Z := 0x82b00.
Definition A_cgif_close : Z := 0x83f54.
Definition A_cgif_newgif : Z := 0x81404.
Definition A_cgif_addframe : Z := 0x81b68.
Definition A_read_frameconfig : Z := 0x80b38.
Definition A_cmpPixel : Z := 0x8291c.
Definition TRAWCLOSE_STK : Z := 32 + ASTACK.
Definition TRAWNEW_STK : Z := 192 + ASTACK.
Definition TRAWADD_STK : Z := 352 + LZW_TSTK.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition tcgif_vals (s : cgif_st) : list Z :=
[ frame_ptr (nth 0 (cg_frames s) None); frame_ptr (nth 1 (cg_frames s) None); frame_ptr (nth 2 (cg_frames s) None);
cg_pal s; 0  ; cg_attr s; cg_gen s; cg_W s; cg_H s; cg_ngp s; cg_loops s;
A_writecb  ; 0  ; cg_raw s; 0  ; cg_cur s; cg_ihead s ].
Definition traw_vals (g : Z) (s : cgif_st) : list Z :=
[ A_cgif_writecb; g; rw_gct s; rw_attr s; cg_W s; cg_H s; raw_sgct s; rw_loops s; rw_cur s ].
Definition tcgif_at (m : word -> option byte) (g : Z) (s : cgif_st) : Prop :=
obj_at tfibsegs m g LAY_CGIF (tcgif_vals s) /\
obj_at tfibsegs m (cg_raw s) LAY_Raw (traw_vals g s) /\
(forall f, In (Some f) (cg_frames s) -> obj_at tfibsegs m (fr_ptr f) LAY_Frame (frame_vals f)).
Definition afobj (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
p mod 8 = 0 /\ range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n.
Definition apost_base (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world tfibsegs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) md' /\
ajournal tfibsegs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
Section e.
Variable B : asyms.
Definition trawclose_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (raw g rcur ctx : Z) rest,
afn_pre tfibsegs B TRAWCLOSE_STK ly S W regs mem md ch ->
getr regs 10 = w64 raw ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: rest) ->
val_mem tfibsegs (mrestrict (w_H W) mem) raw 8 A_cgif_writecb ->
val_mem tfibsegs (mrestrict (w_H W) mem) (raw + 8) 8 g ->
val_mem tfibsegs (mrestrict (w_H W) mem) (raw + 40) 4 rcur -> 0 <= rcur < 2 ^ 32 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_nev S + EV_RAWCLOSE <= EV_MAX ->
In [pc_free_ra0 Tfib_code; 0x86720] (as_universe B) ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_raw_close regs mem md)
(apost_base B TRAWCLOSE_STK (ablocks_fp [(raw, RAW_SIZE)]) regs ly S W mem md EV_RAWCLOSE
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') ((g, CGIF_SIZE) :: rest))).
Definition trawnew_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx : Z) rest,
afn_pre tfibsegs B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX_cgif_raw_newgif -> Z.of_nat (length (frames S)) <= 8 ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp 40 ->
obj_at tfibsegs (mrestrict (w_H W) mem) cfgp LAY_RawConfig [A_cgif_writecb; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: rest) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
st_nev S + EV_RAWNEW <= EV_MAX -> blocks_bytes S + 2 ^ 16 <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_raw_newgif regs mem md)
(apost_base B TRAWNEW_STK [] regs ly S W mem md EV_RAWNEW
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ sgct <= 256 /\
Permutation (ablocks B ly' S') ((res, RAW_SIZE) :: ablocks B ly S) /\
(forall blc i, In (res, RAW_SIZE) blc -> 0 <= i < RAW_SIZE ->
awr_byte TRAWNEW_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (res + i)) /\
aftok [] (ablocks B ly S) (res, RAW_SIZE) /\
obj_at tfibsegs (mrestrict (w_H W') mem') res LAY_Raw [A_cgif_writecb; g; pgct; rattr; Wd; Hd; sgct; loops; R_PENDING])))).
Definition trawadd_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch
(raw g cfp : Z) (gct rattr Wd Hd sgct loops rcur ctx : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)),
afn_pre tfibsegs B TRAWADD_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX_cgif_raw_addframe -> Z.of_nat (length (frames S)) <= 8 ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 raw -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 40 ->
obj_at tfibsegs (mrestrict (w_H W) mem) cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at tfibsegs (mrestrict (w_H W) mem) raw LAY_Raw [A_cgif_writecb; g; gct; rattr; Wd; Hd; sgct; loops; rcur] ->
sgct <= 256 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 56) 8 A_writecb ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem tfibsegs (mrestrict (w_H W) mem) (g + 80) 8 0 ->
1 <= w -> 1 <= h -> w * h <= 100000000 -> w * h <= Nimg ->
Permutation (ablocks B ly S) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
(0 < slct <= 256 -> exists Nl rest', Permutation rest ((lct, Nl) :: rest') /\ 3 * slct <= Nl) ->
st_nev S + EV_RAWADD <= EV_MAX -> blocks_bytes S + LIVE_RAWADD <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_raw_addframe regs mem md)
(apost_base B TRAWADD_STK [(raw + 40, raw + 44)] regs ly S W mem md EV_RAWADD
(fun ly' S' W' regs' mem' md' => exists res rcur' : Z,
getr regs' 10 = w64 res /\ 0 <= res < 2 ^ 64 /\
obj_at tfibsegs (mrestrict (w_H W') mem') raw LAY_Raw [A_cgif_writecb; g; gct; rattr; Wd; Hd; sgct; loops; rcur'] /\
Permutation (ablocks B ly' S') (ablocks B ly S))).
Definition tflush_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (i : nat) (f : frame_st) (rest : list (Z * Z)),
afn_pre tfibsegs B TFLUSH_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_flushFrame -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 g ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = w64 (fr_ptr f) ->
getr regs 12 = w64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_nev S + EV_FLUSH <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_flushFrame regs mem md)
(apost_base B TFLUSH_STK [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] regs ly S W mem md EV_FLUSH
(fun ly' S' W' regs' mem' md' => exists r gen' rwcur' : Z,
getr regs' 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
tcgif_at (mrestrict (w_H W') mem') g (flush_upd s i gen' rwcur') /\ cgif_wf (flush_upd s i gen' rwcur') N /\
Permutation (ablocks B ly' S') (cgif_blocks g s N ++ rest))).
Definition tclose_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z)),
afn_pre tfibsegs B TCLOSE_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_cgif_close -> Z.of_nat (length (frames S)) <= 7 ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 g ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) ->
st_nev S + EV_CLOSE <= EV_MAX -> blocks_bytes S + LIVE_FLUSH <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_close regs mem md)
(apost_base B TCLOSE_STK (ablocks_fp (cgif_blocks g s N)) regs ly S W mem md EV_CLOSE
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest)).
Definition tnewgif_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops : Z) (rest : list (Z * Z)),
afn_pre tfibsegs B TNEWGIF_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX_cgif_newgif -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj B ly S W mem cfgp 48 ->
obj_at tfibsegs (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; 0; attr; gen; Wd; Hd; ngp; loops; A_writecb; 0] ->
Wd * Hd <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
st_nev S + EV_NEWGIF <= EV_MAX -> blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_newgif regs mem md)
(apost_base B TNEWGIF_STK [] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
((res = 0 /\ Permutation (ablocks B ly' S') (ablocks B ly S)) \/
(res <> 0 /\ exists s,
tcgif_at (mrestrict (w_H W') mem') res s /\ cgif_wf s (Wd * Hd) /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (ablocks B ly' S') (cgif_blocks res s (Wd * Hd) ++ ablocks B ly S) /\
(forall b, In b (cgif_blocks res s (Wd * Hd)) ->
aftok [] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIF_STK (spZ regs) [] (ablocks B ly S) blc ly' [] (fst b + i)))))).
Definition taddframe_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (g cfp : Z) (s : cgif_st) (N : Z)
(lpal lpa img fattr fgen delay nlp tidx : Z) (rest : list (Z * Z)),
afn_pre tfibsegs B TADDFRAME_STK ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_cgif_addframe -> Z.of_nat (length (frames S)) <= 7 ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
getr regs 10 = w64 g -> getr regs 11 = w64 cfp ->
afobj B ly S W mem cfp 32 ->
obj_at tfibsegs (mrestrict (w_H W) mem) cfp LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] ->
tcgif_at (mrestrict (w_H W) mem) g s -> cgif_wf s N ->
Z_to_bv 64 lpa = Z_to_bv 64 lpal ->
Permutation (ablocks B ly S)
(cgif_blocks g s N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) ->
st_nev S + EV_ADDFRAME <= EV_MAX -> blocks_bytes S + LIVE_ADDFRAME <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_cgif_addframe regs mem md)
(apost_base B TADDFRAME_STK (ablocks_fp (cgif_blocks g s N)) regs ly S W mem md EV_ADDFRAME
(fun ly' S' W' regs' mem' md' => exists s' : cgif_st,
tcgif_at (mrestrict (w_H W') mem') g s' /\ cgif_wf s' N /\
cg_W s' = cg_W s /\ cg_H s' = cg_H s /\ cg_attr s' = cg_attr s /\ cg_raw s' = cg_raw s /\
Permutation (ablocks B ly' S')
(cgif_blocks g s' N ++ (img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) /\
(forall b, In b (cgif_blocks g s' N) ->
aftok (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TADDFRAME_STK (spZ regs) (ablocks_fp (cgif_blocks g s N)) (ablocks B ly S) blc ly' [] (fst b + i)))).
Definition trfc_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (Bb : list (Z * Z))
(st dst N pdata nb cur : Z) (cid pos : Z) ch,
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall b, In b (ablocks B ly S) -> In b Bb) -> Permutation (ablocks B lyc Sc) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 st -> getr regs 11 = w64 dst -> getr regs 12 = w64 N ->
achain lyc (aview tfibsegs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX_read_frameconfig ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TRFC_STK -> spZ regs <= sp0 ->
In (cid, pos) own -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= dst -> dst + 32 <= frame_addr lyc cid pos + fs_frame_bytes cid -> dst mod 8 = 0 ->
spZ regs <= st -> st + 24 <= sp0 -> st mod 8 = 0 ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF st 24 ->
range_addressable (aview tfibsegs (w_H W) memc) SHADOW_OFF dst 32 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) st 8 pdata -> val_mem tfibsegs (mrestrict (w_H W) memc) (st + 8) 8 nb ->
val_mem tfibsegs (mrestrict (w_H W) memc) (st + 16) 8 cur ->
st_nev S + k + EV_RFC <= EV_MAX -> blocks_bytes Sc + LIVE_RFC <= LIVE_MAX ->
SRr tfibsegs W (cfg_at tfibsegs A_read_frameconfig regs memc mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res cur2 : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_RFC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
getr regs2 10 = w64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - TRFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> aview tfibsegs (w_H W2) mem2 (b + i) = aview tfibsegs (w_H W) memc (b + i)) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) memc a) /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) st 8 pdata /\ val_mem tfibsegs (mrestrict (w_H W2) mem2) (st + 8) 8 nb /\
val_mem tfibsegs (mrestrict (w_H W2) mem2) (st + 16) 8 cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ exists leak, Permutation (ablocks B ly2 S2) (leak ++ Bb) /\
(leak = [] \/ exists lpa nlp, leak = [(lpa, 3 * nlp)] /\ 0 <= nlp < 2 ^ 16) /\
(forall b, In b leak -> aftok FP (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (fst b + i))) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx,
obj_at tfibsegs (mrestrict (w_H W2) mem2) dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\
Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (ablocks B ly2 S2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
(forall b, In b ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) ->
aftok FP (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (fst b + i))))).
End e.
End d.
