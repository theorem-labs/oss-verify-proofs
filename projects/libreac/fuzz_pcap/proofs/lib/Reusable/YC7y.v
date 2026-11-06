(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7y.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI08 YN3v YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YO07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Export YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.
Record xnums : Type := mkXN {
xm_lzw : Z -> Z -> Z;  xn_lzw : Z -> Z -> Z;
xm_rawadd : Z -> Z;    xn_rawadd : Z -> Z;
xm_flush : Z -> Z;     xn_flush : Z -> Z;
xm_addframe : Z -> Z;  xn_addframe : Z -> Z;
xm_close : Z -> Z;     xn_close : Z -> Z;
xm_newgif : Z -> Z;    xn_newgif : Z -> Z }.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition CBB_STK : Z := 96 + ESTACK.
Definition tcbb_specX (a : Z) : Prop :=
forall W ly S regs mem md ch bl Lbl bb Lbb n rest (BL : list Z),
afn_pre segs B CBB_STK ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 bb -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 28 -> n <= Lbl -> cbb_len n <= Lbb ->
Permutation (ablocks B ly S) ((bl, Lbl) :: (bb, Lbb) :: rest) ->
garr8 segs (rdW W mem) bl BL -> Z.of_nat (length BL) = n ->
SRr segs W (cfg_at segs a regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B CBB_STK (spZ regs) (ablocks_fp [(bb, Lbb)]) ly S W mem md [] ly S W mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 (cbb_len n - 1) /\
garr8 segs (rdW W mem') bb (YO07.blocks255 (Datatypes.S (length BL)) BL) /\
Z.of_nat (length (YO07.blocks255 (Datatypes.S (length BL)) BL)) = cbb_len n).
Definition tcbl_specX (stk a : Z) : Prop :=
forall W ly S regs mem md ch bl Lby lz Llz lzwPos D C0 rest (CODES : list Z),
afn_pre segs B stk ly S W regs mem md ch ->
getr regs 10 = w64 bl -> getr regs 11 = w64 lzwPos -> getr regs 12 = w64 lz ->
getr regs 13 = w64 D -> getr regs 14 = w64 C0 ->
0 <= lzwPos < 2 ^ 28 -> 0 <= D <= 65535 -> 0 <= C0 <= 12 ->
12 * lzwPos / 8 + 3 <= Lby -> 2 * lzwPos <= Llz ->
Permutation (ablocks B ly S) ((bl, Lby) :: (lz, Llz) :: rest) ->
arr16 segs (rdW W mem) lz CODES -> Z.of_nat (length CODES) = lzwPos ->
SRr segs W (cfg_at segs a regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' ret,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B stk (spZ regs) (ablocks_fp [(bl, Lby)]) ly S W mem md [] ly S W mem' md' 0 /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 ret /\ 0 <= ret /\ 8 * ret <= 12 * lzwPos /\
garr8 segs (rdW W mem') bl (YO07.create_byte_list D C0 CODES) /\
Z.of_nat (length (YO07.create_byte_list D C0 CODES)) = ret + 1).
Definition lzw_vokA (idl icl : Z) (PIX : list Z) (m : word -> option byte) (bb M : Z) : Prop :=
exists out, YO07.lzw_stream idl icl PIX = Some out /\ garr8 segs m bb out /\ M = Z.of_nat (length out).
Definition lzw_vnone (idl icl : Z) (PIX : list Z) : Prop := YO07.lzw_stream idl icl PIX = None.
Definition tlzw_postX (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (pR nP idl icl : Z) (PIX : list Z) : world segs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + LZW_EV) /\
aregs_preserved regs regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
mo_le MT Sc S2 (xn_lzw XN nP idl) /\
((res = 0 /\
exists bb Lbb M,
Permutation (ablocks B ly2 S2) ((bb, Lbb) :: ablocks B lyc Sc) /\ 4096 <= bb /\ 1 <= M <= Lbb /\ M <= 2 * nP + 16 /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> awr_byte STK sp0 FP (ablocks B ly S) blc ly2 own (bb + i)) /\
aftok FP (ablocks B ly S) (bb, Lbb) /\
val_mem segs (rdW W2 mem2) pR 8 bb /\ val_mem segs (rdW W2 mem2) (pR + 8) 4 M /\
lzw_vokA idl icl PIX (rdW W2 mem2) bb M /\
tlzw_kept segs B lyc Sc W memc W2 mem2 (spZ regs) pR (fun a => bb <= a < bb + req_size Lbb))
\/ (res = 5 /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ lzw_vnone idl icl PIX /\
tlzw_kept segs B lyc Sc W memc W2 mem2 (spZ regs) pR (fun _ => False) /\
(forall a, pR <= a < pR + 12 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a))).
Definition tlzw_specX (a : Z) (CTX : list (list Z)) (rlo rhi : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) ch (PIX : list Z),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memc) ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pR -> getr regs 11 = w64 nP -> getr regs 12 = w64 img ->
getr regs 13 = w64 idl -> getr regs 14 = w64 icl ->
achain lyc (aview segs (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_TSTK -> spZ regs <= sp0 ->
pR mod 8 = 0 -> (spZ regs <= pR \/ pR + 16 <= spZ regs - LZW_TSTK) -> 0 <= pR -> pR + 16 <= 2 ^ 63 ->
(forall x, pR <= x < pR + 16 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\
apresent (w_H W) memc x) ->
tlzw_pR_ok segs lyc Sc W memc pR ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (ablocks B lyc Sc) -> bi <= img -> img + nP <= bi + req_size Li ->
garr8 segs (rdW W memc) img PIX -> Z.of_nat (length PIX) = nP ->
st_nev Sc + LZW_EV <= EV_MAX -> blocks_bytes Sc + 2 ^ 29 <= LIVE_MAX ->
mo_ok MT Sc (xm_lzw XN nP idl) ->
SRr segs W (cfg_at segs a regs memc mdc)
(tlzw_postX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pR nP idl icl PIX).
End d.
End c.
End b.
