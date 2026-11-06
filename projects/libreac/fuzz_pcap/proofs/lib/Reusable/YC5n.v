(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC5n.v, with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI00 YI04 YI09 YI08 YN3v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI5w YI5z YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YO07.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO08 YC5d YC7x YC21.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI17 YE02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Definition TNEWGIFX_STK : Z := 192 + AFOPEN_STK.
Lemma TNEWGIFX_STK_val : TNEWGIFX_STK = 18816. Proof. reflexivity. Qed.
Lemma TNEWGIFX_STK_ge : TNEWGIF_STK <= TNEWGIFX_STK. Proof. vm_compute. discriminate. Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable segs : list Segment.
Variable K : asink_syms.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XN : xnums.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Record afile_meter : Prop := mkAFM {
afm_k0 : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md',
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 0 -> mo_le MT S S' 0;
afm_open : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' f,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 1 ->
ablocks B ly' S' = ablocks B ly S ++ [(f, FILE_BLOCK)] -> mo_le MT S S' (mo_malloc MT FILE_BLOCK);
afm_close : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' f rest,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' 2 ->
Permutation (ablocks B ly S) ((f, FILE_BLOCK) :: rest) -> Permutation (ablocks B ly' S') rest ->
mo_le MT S S' (mo_free MT + mo_free MT) }.
Definition tnewgif_postA (regs : bvmap 5 word) ly S (W : world segs) mem md (Wd Hd attr gen ngp : Z) (GPAL : list Z) (aM : Z) : world segs -> config -> Prop :=
apost_base segs B TNEWGIFX_STK [sink_token] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 0 /\ ameta_ok segs K (rdW W' mem') aM /\ mo_le MT S S' (xn_newgif XN ngp) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\ asink_none segs K (rdW W' mem') md' /\ m_fs md' = m_fs md /\
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> m_fds md' = m_fds md)).
Definition tnewgif_postB0 (regs : bvmap 5 word) ly S (W : world segs) mem md (Wd Hd attr gen ngp : Z) (GPAL : list Z) (aM : Z) : world segs -> config -> Prop :=
apost_base segs B TNEWGIFX_STK [sink_token] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 0 /\ ameta_ok segs K (rdW W' mem') aM /\ mo_le MT S S' (xn_newgif XN ngp) /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\ asink_none segs K (rdW W' mem') md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes [])).
Definition tnewgif_postB1 (wfn : Z) (regs : bvmap 5 word) ly S (W : world segs) mem md (Wd Hd attr gen ngp loops : Z) (GPAL : list Z) (aM : Z) : world segs -> config -> Prop :=
apost_base segs B TNEWGIFX_STK [sink_token] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
ameta_ok segs K (rdW W' mem') aM /\ mo_le MT S S' (xn_newgif XN ngp) /\ res <> 0 /\
exists (s : cgif_st) (f : Z),
xcgif_at segs wfn (ak_path K) 0 f (rdW W' mem') res s /\ cgif_wf s (Wd * Hd) /\ f <> 0 /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\ cg_gen s = gen /\ cg_ngp s = ngp /\
Permutation (ablocks B ly' S') (cgif_blocks res s (Wd * Hd) ++ (f, FILE_BLOCK) :: ablocks B ly S) /\
(forall b, In b (cgif_blocks res s (Wd * Hd) ++ [(f, FILE_BLOCK)]) ->
aftok [sink_token] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc ly' [] (fst b + i)) /\
cgif_relA segs K (rdW W' mem') md' s f (Wd * Hd) GPAL (gs_new Wd Hd attr ngp loops GPAL) /\
Z.of_nat (length (concat (YO07.s_out (gs_new Wd Hd attr ngp loops GPAL)))) <= HDR_OUT).
Definition tnewgif_x (a : Z) (CTX : list (list Z)) (wfn rlo rhi : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) (rest : list (Z * Z)) (GPAL : list Z)
(TA TB : TSet),
AI segs (w_H W) (w_A W) md ->
afn_pre segs B TNEWGIFX_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj segs B ly S W mem cfgp 48 ->
obj_at segs (rdW W mem) cfgp LAY_Config [pal0; ak_path K; attr; gen; Wd; Hd; ngp; loops; 0; 0] ->
Wd * Hd <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
(Z.land attr 4 = 0 -> garr8 segs (rdW W mem) pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
asink_none segs K (rdW W mem) md ->
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None ->
ameta_inv segs K ly (rdW W mem) aM ->
st_nev S + EV_NEWGIF <= EV_MAX -> blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX ->
mo_ok MT S (xm_newgif XN ngp) ->
(forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postA regs ly S W mem md Wd Hd attr gen ngp GPAL aM W' c' -> srealizes segs c' TA) ->
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = false ->
forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postB0 regs ly S W mem md Wd Hd attr gen ngp GPAL aM W' c' -> srealizes segs c' TB) ->
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = true ->
forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postB1 wfn regs ly S W mem md Wd Hd attr gen ngp loops GPAL aM W' c' -> srealizes segs c' TB) ->
srealizes segs (cfg_at segs a regs mem md)
(if g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) then openat_shape (m_fs md) TA TB else TA).
End d.
End c.
