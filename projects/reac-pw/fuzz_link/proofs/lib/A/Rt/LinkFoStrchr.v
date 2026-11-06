(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2j.v, with its module paths changed, TfibSyms renamed PcapSyms, its addresses moved to libreac/fuzz_pcap's v1.9.0 ASan build, and its literal instances replaced by pcap's two (musl fmemopen 0x96a4c / 0x96a60). *)
(* Modified by Theorem Labs, 2026-10: the proof that uses the value of TFIB_IMG_END (now PcapImgEnd.pcap_img_end = YImgTop.IMG_TOP, A/AF0x.v) also unfolds pcap_img_end and YImgTop.IMG_TOP, so the file requires PcapImgEnd and YImgTop; no statement changed. *)
(* Modified by Theorem Labs, 2026-10: deviation from the donor (cgif A/AE2j.v takes ro_img, all of the read-only image): strchr_inst and tfib_strchr_lit take, in place of ro_img, facts for only the image bytes the walk reads -- rwa_img (the one byte of musl's "rwa\0" the walk loads, 0x20026) and A/AE39.v's mconsts_view (__strchrnul's constants, [0x10350, 0x10370)) -- narrowed by porter h-rw-pca-4 (00:10Z / 00:13Z) so musl fmemopen's walk can supply them; strchr_lit_ro_of_img gives both from ro_img. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_link/lib/A/Rt/LinkFoStrchr.v, with its module paths changed. *)
(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d;
   names from its unstripped twin 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f): the two strchr
   calls musl fmemopen makes on link's "w" call, walked from the strchr wrapper's jump 0x43054 to the wrapper's `ret`
   0x44268 (W1 of the fmemopen walks). The theorem fo_strchr_lit proves lib/A/Rt/LinkFoStrchrDef.v afm_strchr_lit for
   every B with PcapSyms B; its only premises are afm_strchr_lit's. The runtime cells the walk reads come from AR,
   PcapSyms and the mode-word premise (fsc_cells), the two "rwa" bytes from the garr8 premise (fsc_rwa_img).
   proves function ___interceptor_strchr (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index ___interceptor_strchr __interceptor_trampoline_strchr __wrap_strchr __interceptor_strchr`)
   proves function strchr (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index strchr`)
   proves function __strchrnul (reuse search: origin/main, origin/ossv/recipes, origin/ossv/candidates, origin/release/pau-projects-recipes / `proof-index __strchrnul`) *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AE2l AF0m AB1w AF0x AE2y AE3i AE39.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YE04 YE00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE2h.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI00 YG0q YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkMfDefs LinkFoSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkFoStrchrDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* Every numeral below is MEASURED on fuzz_link.asan (the pin above; listings under
   link-a/listings/runtime/ (internal records, the sha256 of each in the records MANIFEST)).
   - LA_W_STRCHR 0x43054 (LinkFoStrchrDef.v) = __interceptor_trampoline_strchr, `j` 0x44118 (the wrapper,
     ___interceptor_strchr, 736 B); musl fmemopen's two `jal` (+0x30: strchr (mode, '+'); +0x44: strchr ("rwa",
     mode[0])) call it.
   - SC_RETPC 0x44268 = the wrapper's `ret` (+0x150). The runs never reach its report path (+0x1fc .. +0x2dc).
   - FSC_WIN 2176 (LinkFoStrchrDef.v) = 0x7f0 + 0x70 (the wrapper's `addi sp` +0x00 / +0x2c) + 16 (strchr 0x9b0a0)
     + 16 (__strchrnul 0x9b0dc); TryAsanInitFromRtl (0x5b214) adds 16 at the wrapper's depth only; AsanInited
     (0x5a304) and internal_strlen (0x657f8) use no stack.
   - A_RWA 0x20291 = .rodata "rwa\0" (LinkFoSpec.v LA_RWA; fmemopen +0x3c / +0x40). img_piece A_RWA RWA_LD =
     [0x20291, 0x20293) holds the two bytes of "rwa" the walk loads: 'r' and 'w' (instance 1: __strchrnul's byte
     loop `lbu` 0x9b0fc runs twice, the address being 1 mod 8; strchr's `lbu` 0x9b0b4 reads 'w'); instance 2 never
     reads A_RWA. Its premise is rwa_img, from afm_strchr_lit's `garr8 LA_RWA rwa_Z` (fsc_rwa_img).
     img_piece 0x10360 0x20 = [MC_LO, MC_HI) (A/AE39.v) holds __strchrnul's constants 0x10378 = 0x0101010101010100
     (`auipc` 0x9b118 + `ld` 0x9b11c) and 0x10360 = 0x8080808080808080 (`auipc` 0x9b124 + `ld` 0x9b128), its only
     image loads (instance 2 only); its premise is mconsts_view.
   - A_MODE 0x21260 = .rodata "w\0" (LinkMfDefs.v LA_MODE_W): an ASan global of size 2, the word [0x21260, 0x21268)
     = 0x77 ('w', 0, six 0 bytes), read by __strchrnul's `ld` 0x9b120, its byte loop `lbu` 0x9b19c, strchr's `lbu`
     0x9b0b4 and internal_strlen's `lbu` 0x65800 (instance 2).
   - st_const (AF0m.v Tfib_const_abs): .got 0xa19c0 = 0x13bf68 (the runtime flags pointer; `ld` 0x4417c) and the
     flag words 0x13c058 / 0x13c060 (start-up values): +0xfd = 0x13c065 = 1 (`lbu` 0x44180, the interceptor is on),
     +0xf5 = 0x13c05d = 0 (`lbu` 0x44188, no strict string checks).
   - st_cells: .data 0xa36e8 = 0x9b0a0 REAL(strchr) (`ld` 0x44160; AF0m.v Tfib_const_abs); the shadow words the
     wrapper's range check loads (`ld` 0x4422c / 0x44230, both at the same granule word in each instance): 0x7fffc050
     = 0 (the shadow of 0x20280 .. 0x202bf, which holds "rwa"'s shadow byte 0x7fffc052: AR's zero-shadow law over
     the first row of Tfib_zero_shadow, [0x10000, 0x20fa0)) and 0x7fffc248 = 0xf9f9f902f9f9f903 (bytes 03 f9 f9 f9
     02 f9 f9 f9: the granule 0x21240's 3 addressable bytes and its redzone, then "w"'s partial granule of 2 and its
     redzone; AF0m.v Tfib_const_shadow), whose byte 0x7fffc24c = 2 the `lb` 0x442e0 reads (1 < 2: the last byte
     0x21261 is addressable); and the mode word A_MODE 8 = 0x77, from afm_strchr_lit's `val_mem LA_MODE_W 8 119`.
     fsc_cells derives all four from AR, PcapSyms and that premise.
   - icpt_rodata (A/AE2y.v): asan_inited 0xab118 = 1 (AsanInited's `lb` 0x5a308, TryAsanInitFromRtl's `lb` 0x5b228),
     the shadow-base cell .got 0xa19d0 = 0xaa438 (`ld` 0x44208) and 0xaa438 = 0x7fff8000 (`ld` 0x4420c).
   - The code table tbl_ff (A/AE2l.v) over tbl_icpt (A/AE34.v) holds every word the runs execute: tbl_fsc_probe. *)
Definition SC_RETPC : Z := 0x44268.
Definition A_RWA : Z := 0x20291.
Definition RWA_LD : Z := 2.
Definition A_MODE : Z := 0x21260.
Lemma fsc_consts : A_RWA = LinkFoSpec.LA_RWA /\ A_MODE = LinkMfDefs.LA_MODE_W.
Proof. split; reflexivity. Qed.
(* the trampoline, the wrapper, AsanInited, TryAsanInitFromRtl, internal_strlen, strchr, __strchrnul: (entry, words) *)
Definition fsc_code : list (Z * nat) :=
[ (0x43054, 1%nat); (0x44118, 184%nat); (0x5a304, 6%nat); (0x5b214, 40%nat); (0x657f8, 7%nat); (0x9b0a0, 15%nat);
(0x9b0dc, 56%nat) ].
Lemma tbl_fsc_probe :
forallb (fun r => forallb (fun i => match clookup tbl_ff (fst r + 4 * Z.of_nat i) with Some _ => true | None => false end)
(List.seq 0 (snd r))) fsc_code = true /\
clookup tbl_ff 0x43054 = Some 0x0c40106f /\ clookup tbl_ff 0x44268 = Some 0x00008067 /\
clookup tbl_ff 0x9b0a0 = Some 0xff010113 /\ clookup tbl_ff 0x9b0dc = Some 0xff010113 /\
clookup tbl_ff 0x5a304 = Some 0x00051517 /\ clookup tbl_ff 0x5b214 = Some 0xff010113 /\
clookup tbl_ff 0x657f8 = Some 0x00000593.
Proof. vm_compute. repeat split; reflexivity. Qed.
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
region_ok tfibsegs E (mrestrict (w_H W) mem) (img_piece 0x10360 (0x10380 - 0x10360)).
Proof.
intros W mem E Hmc. pose proof mc_bounds as [MB1 MB2].
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok (YP09.mkChunk 0x10340 (CImg (0x103b0 - 0x10340))) ltac:(unfold img_ro_chunks; cbn; tauto)) as Hz.
cbv beta in Hz.
unfold img_piece, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *. rewrite !Z.add_0_l. cbn [cbyte].
pose proof (YP08.zallb_sound _ _ _ (0x10360 + i) Hz ltac:(cbn [YP09.c_off c_len cv_len YP09.c_val]; rewrite Z2Nat.id by lia; lia)) as Hb.
specialize (Hmc (0x10360 + i) ltac:(lia)). unfold YP08.img_byte_ok in Hb. unfold img_byte in *.
destruct (seg_rom tfibsegs (Z_to_bv 64 (0x10360 + i))) as [b|]; [|discriminate].
exists b. split; [reflexivity|].
pose proof (AF0x.aview_byte (w_H W) mem (0x10360 + i) (bv_unsigned b) Hmc) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.
Lemma strchr_lit_ro_of_img : forall (W : world tfibsegs) mem,
ro_img (mrestrict (w_H W) mem) -> rwa_img (mrestrict (w_H W) mem) /\ mconsts_view W mem.
Proof.
intros W mem Hro. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])). split.
- intros a Ha. unfold A_RWA, RWA_LD in Ha.
apply (img_piece_bytes _ E0 0x20291 2); [| lia].
apply (img_piece_ok _ E0 0x1ce8d (0x20cfc - 0x1ce8d)); [exact Hro | unfold img_ro_chunks; cbn; tauto | lia | lia | lia].
- intros a Ha. pose proof mc_bounds as [MB1 MB2].
destruct (img_piece_bytes _ E0 0x10360 (0x10380 - 0x10360)
(img_piece_ok _ E0 0x10340 (0x103b0 - 0x10340) 0x10360 (0x10380 - 0x10360) Hro ltac:(unfold img_ro_chunks; cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia))
a ltac:(lia)) as (b & Hb1 & Hb2).
unfold aview. rewrite Hb2. unfold img_byte in Hb1. rewrite Hb1. reflexivity.
Qed.
(* The two bytes of "rwa" the walk loads, from afm_strchr_lit's garr8 premise; their image bytes by evaluation. *)
Lemma fsc_garr8_byte : forall m base l j, YI00.garr8 tfibsegs m base l -> (j < length l)%nat ->
mbyte tfibsegs m (base + Z.of_nat j) = Some (Z_to_bv 8 (nth j l 0)).
Proof.
intros m base l j HG Hj. destruct (HG j Hj) as [X R]. specialize (X 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. rewrite X. f_equal. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.
Lemma fsc_rwa_img : forall m, YI00.garr8 tfibsegs m LinkFoSpec.LA_RWA LinkFoSpec.rwa_Z -> rwa_img m.
Proof.
intros m HG a Ha. unfold A_RWA, RWA_LD in Ha.
assert (a = 0x20291 + Z.of_nat 0 \/ a = 0x20291 + Z.of_nat 1) as [-> | ->] by (cbn [Z.of_nat Pos.of_succ_nat]; lia).
- exists (Z_to_bv 8 114). split; [vm_compute; reflexivity|]. exact (fsc_garr8_byte m _ _ 0 HG ltac:(cbn; lia)).
- exists (Z_to_bv 8 119). split; [vm_compute; reflexivity|]. exact (fsc_garr8_byte m _ _ 1 HG ltac:(cbn; lia)).
Qed.
Definition st_const : list (Z * Z * list (Z * N * Z)) :=
[ (0xa19c0, 8, [(0, 8%N, 0x13bf68)]); (0x13c058, 16, [(0, 8%N, 0x101000100000000); (8, 8%N, 0x101010101010101)]) ].
Lemma st_const_chk : forall ly, rodata_chk ly st_const = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition st_cells : list (Z * Z * list (Z * N * Z)) :=
[ (0xa36e8, 8, [(0, 8%N, 0x9b0a0)]); (0x7fffc050, 8, [(0, 8%N, 0)]); (0x7fffc248, 8, [(0, 8%N, 0xf9f9f902f9f9f903)]);
(A_MODE, 8, [(0, 8%N, 0x77)]) ].
Definition stkS : YP09.region := YP09.mkRegion (Some 2%nat) (- FSC_WIN) 0 (- FSC_WIN) 0 [].
Definition memS : smem := [stkS; img_piece A_RWA RWA_LD; img_piece 0x10360 (0x10380 - 0x10360)] ++ map ro_region (icpt_rodata ++ st_const ++ st_cells).
Definition ssS (s c : Z) : sstate := mkSS LA_W_STRCHR (sr_set (sr_set sr_atoms 10%bv (SLit s)) 11%bv (SLit c)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_ff FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition shapeS (res : Z) (ss : sstate) : bool :=
(ss_pc ss =? SC_RETPC) && match ss_resv ss with None => true | _ => false end && reg_is ss 10 (SLit res) && reg_is ss 1 (SOff 1 0) && reg_is ss 2 (SOff 2 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) FSC_KEPT &&
match ss_mem ss with r0 :: _ => obase_eqb (YP09.r_base r0) (Some 2%nat) && (YP09.r_wlo r0 =? - FSC_WIN) && (YP09.r_whi r0 =? 0) | _ => false end &&
forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (skipn 1 (ss_mem ss)).
Lemma fsc_inst_eq : FSC_INST = [(A_RWA, 119, A_RWA + 1); (A_MODE, 43, 0)].
Proof. reflexivity. Qed.
Definition eS1 : sstate := Eval vm_compute in fst (RUN (ssS A_RWA 119)).
Definition eS2 : sstate := Eval vm_compute in fst (RUN (ssS A_MODE 43)).
Lemma r_S1 : RUN (ssS A_RWA 119) = (eS1, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS (A_RWA + 1) eS1 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma r_S2 : RUN (ssS A_MODE 43) = (eS2, RS_stopped (SR_jalr (SOff 1 0))) /\ shapeS 0 eS2 = true. Proof. vm_compute. split; reflexivity. Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
(* The cells of st_cells, from AR, PcapSyms and the mode word (pcap's PFmemopenMW.v fm_cells, for link's cells). *)
Lemma fsc_cells : forall ly S (W : world tfibsegs) mem md,
AR tfibsegs B ly S W mem md -> val_mem tfibsegs (rd W mem) A_MODE 8 119 ->
cells_hold (rd W mem) st_cells.
Proof.
intros ly S W mem md HAR HMODE.
pose proof (proj1 HAR) as HM.
assert (C8 : forall a v, const_chk ly a 8%N v = true -> val_mem tfibsegs (rd W mem) a 8 v).
{ intros a v Hc. exact (tfib_const_lookup B TB ly S (w_H W) mem a 8%nat v HM (const_chk_sound _ _ _ _ Hc)). }
assert (C1 : forall a v, const_chk ly a 1%N v = true -> 0 <= v < 256 -> mbyte tfibsegs (rd W mem) a = Some (Z_to_bv 8 v)).
{ intros a v Hc Hv. pose proof (tfib_const_lookup B TB ly S (w_H W) mem a 1%nat v HM (const_chk_sound _ _ _ _ Hc) 0%nat ltac:(lia)) as X.
  change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. rewrite X. f_equal. unfold YO0f.le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia. reflexivity. }
assert (ZS : forall lo len x, In (lo, len) Tfib_zero_shadow -> SHADOW_OFF + lo / 8 <= x < SHADOW_OFF + lo / 8 + len / 8 ->
  mbyte tfibsegs (rd W mem) x = Some (Z_to_bv 8 0)).
{ intros lo len x Hin Hx. apply AF0x.aview_byte.
  pose proof (YG0s.AR_zshadow_law_ok tfibsegs B ly S W mem md (lo, len) HAR ltac:(right; rewrite (ts_zsh B TB); exact Hin)) as Z0.
  cbn [fst snd] in Z0. specialize (Z0 (x - (SHADOW_OFF + lo / 8)) ltac:(lia)). unfold YG0v.shadow_of_addr in Z0.
  replace (SHADOW_OFF + lo / 8 + (x - (SHADOW_OFF + lo / 8))) with x in Z0 by lia. exact Z0. }
assert (ZS1 : forall x, 0x7fffc050 <= x < 0x7fffc058 -> mbyte tfibsegs (rd W mem) x = Some (Z_to_bv 8 0)).
{ intros x Hx. apply (ZS YImgTop.IMG_LO (0x20fa0 - YImgTop.IMG_LO)); [unfold Tfib_zero_shadow; left; reflexivity |].
  unfold SHADOW_OFF, YImgTop.IMG_LO. change (0x10000 / 8) with 0x2000. change ((0x20fa0 - 0x10000) / 8) with 0x21f4. lia. }
unfold cells_hold, st_cells, A_MODE in *.
repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|]; split; [lia|];
  apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; split; [|split; [cbn; lia | cbn; lia]] |]); [| | | | apply Forall_nil].
- rewrite Z.add_0_r. apply C8. vm_compute. reflexivity.
- intros k Hk. cbn [N.to_nat Pos.to_nat] in Hk.
  replace (YO0f.le_byte 0 (N.to_nat 8) k) with 0
    by (unfold YO0f.le_byte; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity).
  apply ZS1. lia.
- intros k Hk. cbn [N.to_nat Pos.to_nat] in Hk.
  do 8 (destruct k as [|k];
    [ match goal with |- mbyte _ _ ?a = Some (Z_to_bv 8 ?v) =>
        let a' := eval vm_compute in a in let v' := eval vm_compute in v in change a with a'; change v with v' end;
      apply C1; [vm_compute; reflexivity | lia] |]).
  lia.
- rewrite Z.add_0_r. exact HMODE.
Qed.
Lemma strchr_inst : forall s c res eS,
RUN (ssS s c) = (eS, RS_stopped (SR_jalr (SOff 1 0))) -> shapeS res eS = true -> 0 <= s < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= res < 2 ^ 64 ->
forall ly S (W : world tfibsegs) regs mem md,
AR tfibsegs B ly S W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + FSC_WIN <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - FSC_WIN <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 s -> getr regs 11 = w64 c ->
cells_hold (mrestrict (w_H W) mem) st_cells -> rwa_img (mrestrict (w_H W) mem) -> mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs LA_W_STRCHR regs mem md) (fsc_post B ly S W regs mem md res).
Proof.
intros s c res eS r_S Hsh Rs Rc Rres ly S W regs mem md HAR Hra Hal16 Hslo Hshi HpresE G10 G11 HCELLS HRWA HMC.
unfold fsc_post.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
unfold FSC_WIN in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at at 1. change (w64 LA_W_STRCHR) with (Z_to_bv 64 LA_W_STRCHR).
assert (HS0 : st_ok tfibsegs EE (ssS s c) (restrict H (mkst regs (Z_to_bv 64 LA_W_STRCHR) mem (seg_rom tfibsegs)))).
{ unfold ssS.
apply (st_ok_pin_reg EE (mkSS LA_W_STRCHR (sr_set sr_atoms 10%bv (SLit s)) memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 11%bv (SLit c));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11; reflexivity].
apply (st_ok_pin_reg EE (mkSS LA_W_STRCHR sr_atoms memS None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] [])) _ 10%bv (SLit s));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
rewrite restrict_mkst_fx. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold memS. apply Forall_cons.
{ unfold stkS, FSC_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2176)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia. }
apply Forall_cons; [exact (rwa_piece_ok _ EE HRWA)|].
apply Forall_cons; [exact (mconsts_piece_ok W mem EE HMC)|].
rewrite !map_app. apply Forall_app. split; [exact (AE2y.icpt_rodata_ok B TB ly S H mem EE (proj1 HAR))|].
apply Forall_app. split; [exact (rodata_ok B TB st_const ly S H mem EE (st_const_chk ly) (proj1 HAR))|].
exact (cells_region_ok _ EE st_cells HCELLS).
- apply pairwise_disjoint_of_extents. unfold memS, stkS, img_piece, st_cells, st_const, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_MODE, A_RWA, RWA_LD, FSC_WIN in *. repeat split; lia.
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
apply obase_eqb_eq in W0a. apply Z.eqb_eq in W0b. apply Z.eqb_eq in W0c. unfold FSC_WIN, SC_RETPC in W0b, W0c, Hpc.
assert (RD : forall (r : bv 5) v, reg_is eS (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eS ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) FSC_KEPT -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2176 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2176 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eS ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia].
rewrite W0a, W0b, W0c. cbn [base_val]. rewrite EE2. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [|destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|]];
(apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]). }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2176)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply AE2y.aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat1)).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
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
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold FSC_KEPT in Hin; cbn in Hin; lia).
apply (RK (Z_to_bv 5 r) (Z.to_nat r)); [| rewrite Z2Nat.id by lia; exact Hin].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. }
split; [exact AV1|]. split; [exact PRS1 | exact PM1].
Qed.
End d.
(* The theorem: the two instances, with the cells derived from AR, PcapSyms and the mode word, and the two "rwa"
   bytes from the garr8 premise. *)
Theorem fo_strchr_lit : forall B, PcapSyms B -> afm_strchr_lit B.
Proof.
intros B TB s c res Hin ly S W regs mem md HAR Hra Hal16 Hslo Hshi HpresE G10 G11 HMODE HRWA HMC.
pose proof (fsc_cells B TB ly S W mem md HAR HMODE) as HCELLS.
pose proof (fsc_rwa_img _ HRWA) as HR.
rewrite fsc_inst_eq in Hin. unfold A_RWA, A_MODE in Hin. cbn [In Z.add] in Hin.
destruct Hin as [E|[E|[]]]; injection E as <- <- <-;
[ eapply (strchr_inst B (YG0q.AR_laws_ok tfibsegs B) TB _ _ _ eS1 (proj1 r_S1) (proj2 r_S1))
| eapply (strchr_inst B (YG0q.AR_laws_ok tfibsegs B) TB _ _ _ eS2 (proj1 r_S2) (proj2 r_S2)) ]; try eassumption; unfold A_RWA, A_MODE; lia.
Qed.
End b.
About fo_strchr_lit.
Print Assumptions fo_strchr_lit.
