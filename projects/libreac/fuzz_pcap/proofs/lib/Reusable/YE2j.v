From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/cgif/cgif_file_fuzzer/lib/YE2j.v (ossv/recipes) to libreac/fuzz_pcap's v1.9.0 ASan+UBSan build (the asan-ubsan pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a), with its module paths changed, TfibSyms renamed PcapSyms, its addresses moved by symbol + offset to that pin, and its literal instances replaced by pcap's two (musl fmemopen 0x8e76c / 0x8e780), as lib/A/AE2j.v (a working branch b6db5febb7f) re-keyed cgif's lib/A/AE2j.v on the asan pin. *)
(* Modified by Theorem Labs, 2026-10: deviation from the donor, carried from lib/A/AE2j.v (cgif YE2j.v takes ro_img, all of the read-only image): strchr_inst and tfib_strchr_lit take, in place of ro_img, facts for only the image bytes the walk reads -- rwa_img (the one byte of musl's "rwa\0" the walk loads, 0x20026) and YE39.v's mconsts_view (__strchrnul's constants, [0x10350, 0x10370)) -- so that musl fmemopen's walk (lib/B/Stdio/PFmemopenMW.v, hypothesis SCHR) can supply them; strchr_lit_ro_of_img gives both from ro_img. The proof that uses the value of TFIB_IMG_END (YF0x.v: PcapImgEnd.pcap_img_end = YImgTop.IMG_TOP) unfolds both, so the file requires PcapImgEnd and YImgTop. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE2j.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YB1v YE34 YE2l YF0m YB1w YF0x YE2y YE3i YE39 YE04 YE00 YE2h.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YP08.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* Every numeral below is MEASURED on fuzz_pcap.asan-ubsan v1.9.0 (the stripped pin, sha256 9e66f771f22a; names from
   its own unstripped twin fuzz_pcap.asan-ubsan (sha256 c969d83cdd59)), keyed by symbol + offset. The asan-ubsan bodies
   of ___interceptor_strchr (0x2e0), strchr (0x3c), __strchrnul (0xe0) and fmemopen (0x1d0) are mnemonic- and
   register-identical to the asan pin's word for word; only pc-relative immediates differ.
   - SC_ENTRY 0x415b8 = __interceptor_trampoline_strchr (word 0x2f10006f, `j` 0x420a8 ___interceptor_strchr); musl
     fmemopen's (0x8e73c) two `jal` at 0x8e76c (fmemopen+0x30, strchr (mode, '+')) and 0x8e780 (fmemopen+0x44,
     strchr ("rwa", mode[0])) both call it. (asan 0x41568)
   - SC_RETPC 0x421f8 = the interceptor's `ret` (___interceptor_strchr + 0x150). (asan 0x421a8)
   - SC_WIN 2176 = 0x7f0 + 0x70 (interceptor: `addi sp` 0x420a8 / 0x420d4) + 16 (strchr 0x92f24) + 16
     (__strchrnul 0x92f60); __asan::TryAsanInitFromRtl (0x598e4) adds 16 at the interceptor's depth only.
   - A_RWA 0x20026 = .rodata "rwa\0" (bytes 72 77 61 00), formed by `auipc`/`addi` 0x8e778 / 0x8e77c
     (fmemopen+0x3c / +0x40, words 0xfff92517 / 0x8ae50513).
   - A_RB 0x20d40 = .rodata .str "rb\0" (bytes 72 62 00): the mode pcap_source_open (0x811e0) forms with `auipc`/`addi`
     0x812e8 / 0x812ec (+0x108 / +0x10c) and passes to libreac_fuzz_fopen (0x80788), which tail-calls fmemopen
     through its trampoline 0x41614 (`j` at 0x807fc; the trampoline jumps to __interceptor_fmemopen 0x46694). It is an
     ASan global of size 3 with its redzone to 0x20d60 (asan_globals entry 0x9e010: 0x20d40, 3, 0x20; asan 0x9e140).
   - img_piece A_RWA RWA_LD = [0x20026, 0x20027) is the one byte of A_RWA the walk loads ('r': __strchrnul's `lbu`
     0x92f80 and strchr's `lbu` 0x92f38 in instance 1; instance 2 never reads A_RWA); its premise is rwa_img. It lies
     in YE3i.v's image chunk [0x1cc6d, 0x20a80). img_piece 0x10350 0x20 = [MC_LO, MC_HI) (YE39.v) holds __strchrnul's
     constants 0x10350 = 0x8080808080808080 (`auipc` 0x92fa8 + `ld` 0x92fac) and 0x10368 = 0x0101010101010100 (`auipc`
     0x92f9c + `ld` 0x92fa0), its only image loads (instance 2 only); its premise is mconsts_view. It lies in YE3i.v's
     chunk [0x10330, 0x10398).
   - st_const: .got 0x996e8 = 0x1332e8 __sanitizer::common_flags_dont_use (image value; `auipc` 0x42108 + `ld`
     0x4210c). Its bytes 0xf0..0xff at 0x1333d8 are .bss, so start-up state (YF0m.v's Tfib_const 0x1333d8 / 0x1333e0):
     +0xfd intercept_strchr = 1 (`lbu` 0x42110), +0xf5 strict_string_checks = 0 (`lbu` 0x42118). (asan .got 0x99820
     = 0x1333e8, bytes at 0x1334d8)
   - st_cells: .data 0x9b408 __interception::real_strchr = 0x92f24 strchr (image value; `auipc` 0x420ec + `ld` 0x420f0;
     asan 0x9b540 = 0x93058). The shadow words 0x7fffc000 (shadow of 0x20000..0x2003f; A_RWA's shadow byte is
     0x7fffc004) = 0 and 0x7fffc1a8 (shadow of 0x20d40..0x20d7f) = 0xf9f9f903 (bytes 03 f9 f9 f9 00 00 00 00: "rb"
     partial 3, redzone to 0x20d60, then the unpoisoned 0x20d60..0x20d7f) are start-up state (__asan_register_globals;
     YF0m.v's Tfib_const_shadow 0x7fffc1a8..0x7fffc1ab and Tfib_zero_shadow), read by the `ld` 0x421bc / 0x421c0 and
     the `lb` 0x42270. A_RB 8 = 0x6272 (image bytes 72 62 00 00 00 00 00 00: the literal and 5 redzone bytes), read by
     __strchrnul's `ld` 0x92fa4, its byte loop 0x93020, strchr's `lbu` 0x92f38 and internal_strlen's `lbu` 0x63dbc. *)
Definition SC_ENTRY : Z := (symaddr Symbols.AsanUbsan.s___wrap_strchr).
Definition SC_RETPC : Z := (symaddr (Symbols.AsanUbsan.s___interceptor_strchr + 0x150)%Z).
Definition SC_WIN : Z := 2176.
Definition A_RWA : Z := (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xfd46)%Z).
Definition A_RB : Z := (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68192)%Z).
Definition RWA_LD : Z := 1.
(* rwa_img m: each byte of "rwa\0" the walk loads, [A_RWA, A_RWA + RWA_LD), is in m the image's byte, in the sense of
   ro_img's CImg chunks (YP09.chunk_ok). *)
Definition rwa_img (m : word -> option byte) : Prop :=
forall a, A_RWA <= a < A_RWA + RWA_LD -> exists b, img_byte tfibsegs a = Some b /\ mbyte tfibsegs m a = Some b.
Lemma img_piece_bytes : forall m E a n, region_ok tfibsegs E m (img_piece a n) ->
forall x, a <= x < a + n -> exists b, img_byte tfibsegs x = Some b /\ mbyte tfibsegs m x = Some b.
Proof.
intros m E a n (_ & _ & _ & HC) x Hx. unfold img_piece in HC. cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply Forall_inv in HC. specialize (HC (x - a)). cbn [YP09.c_off YP09.c_val c_len cv_len cbyte] in HC.
destruct (HC ltac:(lia)) as (b & Hb1 & Hb2). exists b. rewrite !Z.add_0_l in Hb1, Hb2.
replace (a + (x - a)) with x in Hb1, Hb2 by lia. exact (conj Hb1 Hb2).
Qed.
Lemma rwa_piece_ok : forall m E, rwa_img m -> region_ok tfibsegs E m (img_piece A_RWA RWA_LD).
Proof.
intros m E Hr. unfold img_piece, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_RWA, RWA_LD in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *. rewrite !Z.add_0_l. cbn [cbyte]. apply Hr. unfold A_RWA, RWA_LD. lia.
Qed.
Lemma mconsts_piece_ok : forall (W : world tfibsegs) mem E, mconsts_view W mem ->
region_ok tfibsegs E (mrestrict (w_H W) mem) (img_piece (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z))).
Proof.
intros W mem E Hmc. pose proof mc_bounds as [MB1 MB2].
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok (YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xb8)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z)))) ltac:(unfold img_ro_chunks; cbn; tauto)) as Hz.
cbv beta in Hz.
unfold img_piece, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *. rewrite !Z.add_0_l. cbn [cbyte].
pose proof (YP08.zallb_sound _ _ _ ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) + i) Hz ltac:(cbn [YP09.c_off c_len cv_len YP09.c_val]; rewrite Z2Nat.id by lia; lia)) as Hb.
specialize (Hmc ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) + i) ltac:(lia)). unfold YP08.img_byte_ok in Hb. unfold aview in Hmc. cbv beta in Hmc. unfold img_byte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) + i))) as [b|]; [|discriminate].
exists b. split; [reflexivity|].
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) + i)) as [b'|]; cbn in Hmc; [|discriminate].
injection Hmc as Hmc. f_equal. apply bv_eq. exact Hmc.
Qed.
Lemma strchr_lit_ro_of_img : forall (W : world tfibsegs) mem,
ro_img (mrestrict (w_H W) mem) -> rwa_img (mrestrict (w_H W) mem) /\ mconsts_view W mem.
Proof.
intros W mem Hro. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])). split.
- intros a Ha. unfold A_RWA, RWA_LD in Ha.
apply (img_piece_bytes _ E0 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xfd46)%Z) 1); [| lia].
apply (img_piece_ok _ E0 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67488)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z))); [exact Hro | unfold img_ro_chunks; cbn; tauto | lia | lia | lia].
- intros a Ha. pose proof mc_bounds as [MB1 MB2].
destruct (img_piece_bytes _ E0 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z))
(img_piece_ok _ E0 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xb8)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z)) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z)) Hro ltac:(unfold img_ro_chunks; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia))
a ltac:(lia)) as (b & Hb1 & Hb2).
unfold aview. rewrite Hb2. unfold img_byte in Hb1. rewrite Hb1. reflexivity.
Qed.
Definition st_const : list (Z * Z * list (Z * N * Z)) :=
[ ((symaddr (Symbols.AsanUbsan.Sec.s_got + 0x50)%Z), 8, [(0, 8%N, (symaddr Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE))]); ((symaddr (Symbols.AsanUbsan.s__ZN11__sanitizer21common_flags_dont_useE + 0xf0)%Z), 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)]) ].
Lemma st_const_chk : forall ly, rodata_chk ly st_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition st_cells : list (Z * Z * list (Z * N * Z)) :=
[ ((symaddr Symbols.AsanUbsan.s__ZN14__interception11real_strchrE), 8, [(0, 8%N, (symaddr Symbols.AsanUbsan.s_strchr))]); (0x7fffc000, 8, [(0, 8%N, 0)]); ((symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 68192) / 8 + 0x7fff8000)%Z), 8, [(0, 8%N, 0xf9f9f903)]); (A_RB, 8, [(0, 8%N, 0x6272)]) ].
Definition stkS : YP09.region := YP09.mkRegion (Some 2%nat) (- SC_WIN) 0 (- SC_WIN) 0 [].
Definition memS : smem := [stkS; img_piece A_RWA RWA_LD; img_piece (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z) ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x90)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x70)%Z))] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells).
Definition ssS (s c : Z) : sstate := mkSS SC_ENTRY (sr_set (sr_set sr_atoms 10%bv (SLit s)) 11%bv (SLit c)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ff FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition KEPTS : list Z := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeS (res : Z) (ss : sstate) : bool :=
(ss_pc ss =? SC_RETPC) && match ss_resv ss with None => true | _ => false end && reg_is ss 10 (SLit res) && reg_is ss 1 (SOff 1 0) && reg_is ss 2 (SOff 2 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTS &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - SC_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Definition INST : list (Z * Z * Z) := [(A_RWA, 114, A_RWA); (A_RB, 43, 0)].
Definition eS1 : sstate := Eval vm_compute in fst (RUN (ssS A_RWA 114)).
Definition eS2 : sstate := Eval vm_compute in fst (RUN (ssS A_RB 43)).
Lemma r_S1 : RUN (ssS A_RWA 114) = (eS1, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS A_RWA eS1 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma r_S2 : RUN (ssS A_RB 43) = (eS2, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS 0 eS2 = true. Proof. vm_compute. split; reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
Lemma strchr_inst : forall s c res eS,
RUN (ssS s c) = (eS, RS_stopped (SR_jalr (SOff 1 0))) -> shapeS res eS = true -> 0 <= s < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= res < 2 ^ 64 ->
forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + SC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 s -> getr regs 11 = w64 c ->
cells_hold (mrestrict (w_H W) mem) st_cells -> rwa_img (mrestrict (w_H W) mem) -> mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs SC_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs (raZ regs) regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 res /\ getr regs1 1 = getr regs 1 /\ getr regs1 2 = getr regs 2 /\
(forall r, In r KEPTS -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a)).
Proof.
intros s c res eS r_S Hsh Rs Rc Rres ly S W regs mem md HAR Hra Hal16 Hslo Hshi HpresE G10 G11 HCELLS HRWA HMC.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold SC_WIN in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof YF0x.Hwx_tfa as Hwx.
set (EE := YE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 SC_ENTRY) with (Z_to_bv 64 SC_ENTRY).
assert (HS0 : st_ok tfibsegs EE (ssS s c) (restrict H (mkst regs (Z_to_bv 64 SC_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssS.
apply (st_ok_pin_reg EE (mkSS SC_ENTRY (sr_set sr_atoms 10%bv (SLit s)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 11%bv (SLit c));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
apply (st_ok_pin_reg EE (mkSS SC_ENTRY sr_atoms memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 10%bv (SLit s));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
rewrite restrict_mkst_fx. unfold EE, YE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memS. apply Forall_cons.
{ unfold stkS. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2176)); [exact EE2 | lia | lia |].
intros a Ha. apply YE2y.apresent_writable. apply HpresE. subst sp0. lia. }
apply Forall_cons; [exact (rwa_piece_ok _ EE HRWA)|].
apply Forall_cons; [exact (mconsts_piece_ok W mem EE HMC)|].
rewrite !map_app. apply Forall_app. split; [exact (YE2y.icpt_rodata_ok B TB ly S H mem EE (proj1 HAR))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem EE (st_const_chk ly) (proj1 HAR))|].
exact (cells_region_ok _ EE st_cells HCELLS).
- apply pairwise_disjoint_of_extents. unfold memS, stkS, img_piece, st_cells, st_const, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_RB, A_RWA, RWA_LD, SC_WIN in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2. change (2 ^ 4) with 16. repeat split; try lia; exact Hal16. }
eapply SRr_bind; [exact (ff_phase W EE (ssS s c) eS _ _ md HS0 r_S)|].
intros W1' c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ~ (sp0 - 2176 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
pose proof (in_wrange_single_b EE memS (bv_unsigned z) 2 (- 2176) 0 sp0 ltac:(vm_compute; reflexivity) EE2 Hin). lia. }
clear HF1 HFr1.
unfold shapeS in Hsh.
apply andb_prop in Hsh as [Hsh Hro]. apply andb_prop in Hsh as [Hsh Hwin]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv : ss_resv eS = None) by (destruct (ss_resv eS); [discriminate | reflexivity]).
destruct (ss_mem eS) as [|r0 rest] eqn:Hmem; [discriminate |].
apply andb_prop in Hwin as [Hwin W0c]. apply andb_prop in Hwin as [W0a W0b].
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold SC_WIN, SC_RETPC in W0b, W0c, Hpc.
assert (RD : forall (r : bv 5) v, reg_is eS (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eS ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTS -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2176 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2176 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eS ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (YE2y.apresent_mod _ (ms_mem ms1) a). rewrite (YE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (YE2y.aview_mod _ (ms_mem ms1) a). rewrite (YE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply YE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ exact (YE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
eapply (SRr_ret_at tfibsegs tbl_ff tbl_ff_ok Hwx W EE); [exact HS1 | exact Hresv | rewrite Hpc; vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|].
assert (P1 : getr (ms_regs ms1) 1 = getr regs 1) by (rewrite (RD 1%bv (SOff 1 0) R1); cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HAR2 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat' md)).
{ assert (SBM : same_but_materialized (with_vm_backing (m_vm_lazy md) mat1 md) (with_vm_backing (m_vm_lazy md) mat' md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) mat' mat1 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM) as MF.
apply (al_frame _ _ LAWS ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md) (ms_mem ms1) _ HAR1);
[intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | intros a _ _; reflexivity]. }
exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [unfold cfg_at; rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply with_vm_backing_same|]. split; [exact HAR2|].
split; [rewrite (RD 10%bv (SLit res) R10); reflexivity|].
split; [exact P1|].
split; [rewrite (RD 2%bv (SOff 2 0) R2); cbn [sv_denot]; rewrite (EEreg 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTS in Hin; cbn in Hin; lia).
apply (RK (Z_to_bv 5 r) (Z.to_nat r)); [| rewrite Z2Nat.id by lia; exact Hin].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.
Definition strchr_post (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (res : Z)
: world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs1 mem1 md1,
c' = cfg_at tfibsegs (raZ regs) regs1 mem1 md1 /\ same_but_materialized md md1 /\ AR tfibsegs B ly S W mem1 md1 /\
getr regs1 10 = w64 res /\ getr regs1 1 = getr regs 1 /\ getr regs1 2 = getr regs 2 /\
(forall r, In r KEPTS -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SC_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem1 a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a).
Theorem tfib_strchr_lit : forall s c res, In (s, c, res) INST ->
forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + SC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - SC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 s -> getr regs 11 = w64 c ->
cells_hold (mrestrict (w_H W) mem) st_cells -> rwa_img (mrestrict (w_H W) mem) -> mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs SC_ENTRY regs mem md) (strchr_post ly S W regs mem md res).
Proof.
intros s c res Hin. unfold INST, A_RWA, A_RB in Hin. cbn [In Z.add] in Hin.
destruct Hin as [E|[E|[]]]; injection E as <- <- <-; intros;
[ eapply (strchr_inst _ _ _ eS1 (proj1 r_S1) (proj2 r_S1))
| eapply (strchr_inst _ _ _ eS2 (proj1 r_S2) (proj2 r_S2)) ]; try eassumption; unfold A_RWA, A_RB; lia.
Qed.
End d.
End b.
