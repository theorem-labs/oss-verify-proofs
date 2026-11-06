(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* reac_box_catalogue_defect of fuzz_identity.asan-ubsan (build B), at BASE + AF_reac_box_catalogue_defect = 0x83944:
   the contract and its walk, the B twin of lib/A/Prog/reac_box_catalogue_defect.v (same names,
   same statement except as listed below, same proof structure;
   the module path distinguishes them). The function takes a 16-byte frame (ra, s0), returns 0 when e = 0, and
   otherwise traps (UBSan alignment of the `const struct reac_box_model *`, 0x83958 -> `unimp` at 0x83a00) unless
   e mod 8 = 0, reads I at e+16 and O at e+20 (ASan 4-byte checks, __asan_report_load4 at 0x83a14 / 0x83a28 on
   the error path), sets s0 to 0 when I = i and O = o and to 1 otherwise, returns s0 when d = 0, reads P at e+8 (ASan
   8-byte check, __asan_report_load8 at 0x83a2c), returns s0 when P = 0, and otherwise calls the strcmp wrapper on
   (P, d) and returns s0 | 2 * (strcmp <> 0). Measured on the B listing:
   59 slots (A: 56), the same frame (16 bytes,
   STK = 16 + 2 * ESTACK, the strcmp window), the same 4 calls; one more branch (the alignment trap).
   B differences from A: the premise `e mod 8 = 0` in the e <> 0 block (the UBSan alignment trap at 0x83958; with it
   the pointer fact of a0 carries e mod 8 = 0 and the engine computes a4 = e & 7 = 0, so the trap is not reached);
   the shadow cell is object 31 of the B listing (A: 30, IdentBPaLib.v pal_cell), in the premise that keeps e's
   bytes apart from it; the listing / symbols / strcmp entry are the B ones (identb_listing, PL_identb,
   IB___interceptor_trampoline_strcmp, lib/B/Rt/StrcmpDef.v). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep PaRun PaShadow PaJournal IdentBase IdentRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSyms IdentBList IdentBPa IdentBPaLib.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_catalogue_defect_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB_CD : Z := 0x7fff8000.
Definition CDBx : sv := SOff 35 0.
Definition CDBspan : Z * Z := (SB_CD, SB_CD + 2 ^ 44 - 1).
Definition cd_eregion : YP09.region :=
YP09.mkRegion (Some 10%nat) 8 24 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 4 (SOff 33 0)); YP09.mkChunk 20 (CVal 4 (SOff 34 0))].
Definition cd_regions : smem := [stack_region 16; got_regionP; bcell_regionP 35; cd_eregion].
(* B: atom 10 (e) carries e mod 2 ^ 3 = 0, which decides the UBSan alignment check at 0x83954..0x83958. *)
Definition cd_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 0x8000 IMG_TOP 3);
(33%nat, mkAF 0 4294967295 0); (34%nat, mkAF 0 4294967295 0); (35%nat, mkAF SB_CD SB_CD 0)] [] [].
Definition ss_cd : sstate := mkSS AF_reac_box_catalogue_defect sr_atoms cd_regions None cd_facts.
Definition cd_SH : list shent := [mkSHE 10 8 24].
Definition ss_cd0 : sstate :=
mkSS AF_reac_box_catalogue_defect sr_atoms [stack_region 16] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Fixpoint catd_k (x y : list byte) : nat :=
match x, y with
| a :: x', b :: y' => if bv_unsigned a =? bv_unsigned b then S (catd_k x' y') else O
| _, _ => O
end.
Definition catd_lz (s : list byte) : list Z := map (fun b : byte => bv_unsigned b) s ++ [0].
Lemma catd_lz_len : forall s, length (catd_lz s) = S (length s).
Proof. induction s as [|a s IH]; [reflexivity|]. unfold catd_lz in *. cbn [map app length]. rewrite IH. reflexivity. Qed.
Lemma catd_byte0 : forall b : byte, b <> Z_to_bv 8 0 -> bv_unsigned b <> 0.
Proof. intros b H E. apply H. apply bv_eq. rewrite E. reflexivity. Qed.
Lemma catd_k_le : forall x y : list byte, (catd_k x y <= length x)%nat /\ (catd_k x y <= length y)%nat.
Proof.
induction x as [|a x IH]; intros [|b y]; cbn [catd_k length]; try lia.
destruct (bv_unsigned a =? bv_unsigned b); [destruct (IH y); lia | lia].
Qed.
Lemma catd_k_spec : forall x y, ~ In (Z_to_bv 8 0) x -> ~ In (Z_to_bv 8 0) y ->
(forall j, (j < catd_k x y)%nat -> nth j (catd_lz x) 0 = nth j (catd_lz y) 0 /\ nth j (catd_lz x) 0 <> 0) /\
(nth (catd_k x y) (catd_lz x) 0 <> nth (catd_k x y) (catd_lz y) 0 \/ nth (catd_k x y) (catd_lz x) 0 = 0) /\
(nth (catd_k x y) (catd_lz x) 0 = nth (catd_k x y) (catd_lz y) 0 <-> x = y).
Proof.
induction x as [|a x IH]; intros [|b y] Nx Ny; unfold catd_lz in *; cbn [catd_k map app nth] in *.
- split; [intros j Hj; lia|]. split; [right; reflexivity|]. split; intros; reflexivity.
- split; [intros j Hj; lia|]. split; [right; reflexivity|].
split; [intros H; exfalso; apply (catd_byte0 b); [intros ->; apply Ny; left; reflexivity | lia] | discriminate].
- split; [intros j Hj; lia|].
split; [left; apply catd_byte0; intros ->; apply Nx; left; reflexivity|].
split; [intros H; exfalso; apply (catd_byte0 a); [intros ->; apply Nx; left; reflexivity | lia] | discriminate].
- destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [Eab|Nab].
+ destruct (IH y) as (P1 & P2 & P3); [intros H; apply Nx; right; exact H | intros H; apply Ny; right; exact H |].
split; [intros [|j] Hj; cbn [nth]; [split; [exact Eab | apply catd_byte0; intros ->; apply Nx; left; reflexivity] | apply P1; lia]|].
cbn [nth]. split; [exact P2|].
rewrite P3. split; [intros ->; f_equal; apply bv_eq; exact Eab | intros H; injection H as _ H; exact H].
+ split; [intros j Hj; lia|]. split; [left; exact Nab|].
split; [intros H; contradiction | intros H; injection H as H _; subst; contradiction].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition A_reac_box_catalogue_defectP : Z := BASE + AF_reac_box_catalogue_defect.
Definition REAC_BOX_CATALOGUE_DEFECT_STK : Z := 16 + 2 * ESTACK.
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Definition catd_glob (a n : Z) : Prop :=
exists q z, In (q, z) G /\ q <= a /\ a + n <= q + z.
Definition catd_rostr (W : world SEGS) (mem : word -> option byte) (x : Z) (s : list byte) : Prop :=
garr8 SEGS (mrestrict (w_H W) mem) x (catd_lz s) /\ ~ In (Z_to_bv 8 0) s /\
catd_glob x (Z.of_nat (length s) + 1) /\
IMG_LO + 64 <= x /\ x + Z.of_nat (length s) + 1 + 64 <= IMG_TOP.
Definition catd_hpstr ly S (W : world SEGS) (mem : word -> option byte) (x : Z) (s : list byte) : Prop :=
garr8 SEGS (mrestrict (w_H W) mem) x (catd_lz s) /\ ~ In (Z_to_bv 8 0) s /\
exists n, In (x, n) (ablocks B ly S) /\ Z.of_nat (length s) + 1 <= n.
Definition treac_box_catalogue_defect_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
(e i o d I O P : Z) (sP sd : list byte) : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_BOX_CATALOGUE_DEFECT_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o d I O P sP sd) /\
ly' = ly /\ S' = S /\ W' = W /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_BOX_CATALOGUE_DEFECT_STK <= a < spZ regs) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition treac_box_catalogue_defect_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (e i o d I O P : Z) (sP sd : list byte),
afn_pre SEGS B REAC_BOX_CATALOGUE_DEFECT_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> getr regs 11 = w64 i -> getr regs 12 = w64 o -> getr regs 13 = w64 d ->
0 <= e < 2 ^ 64 -> -2 ^ 31 <= i < 2 ^ 31 -> -2 ^ 31 <= o < 2 ^ 31 -> 0 <= d < 2 ^ 64 ->
-2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
(e <> 0 ->
IMG_LO <= e + 8 /\ e + 24 <= IMG_TOP /\ catd_glob (e + 8) 16 /\
e mod 8 = 0 /\
(e + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= e + 8) /\
(e + 24 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= e + 8) /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 8 P /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 4 I /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 O) ->
(e <> 0 -> d <> 0 -> P <> 0 -> catd_rostr W mem P sP /\ catd_hpstr ly S W mem d sd) ->
SRr SEGS W (cfg_at SEGS A_reac_box_catalogue_defectP regs mem md)
(treac_box_catalogue_defect_post regs ly S W mem md e i o d I O P sP sd).
Definition cd_extra (P Iu Ou : Z) : list word := map (Z_to_bv 64) [P; Iu; Ou; SB_CD].
Lemma catd_U_atom_mod : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = v mod 2 ^ 64.
Proof.
intros E n v H. rewrite U_SOff, H, Z.add_0_r, Z_to_bv_unsigned. unfold zcanon, bv_wrap, M64.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma catd_sext : forall E n I, ew E n = Z_to_bv 64 (I mod 2 ^ 32) -> -2 ^ 31 <= I < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = I mod 2 ^ 64.
Proof.
intros E n I Hn HI. pose proof (Z.mod_pos_bound I (2 ^ 32) ltac:(lia)) as R.
rewrite U_SExt, (U_atom E n (I mod 2 ^ 32) Hn) by lia.
change (Z.of_N 32) with 32. rewrite Z.mod_mod by lia.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
Z.div_mod_to_equations. lia.
Qed.
Lemma catd_val_mem_mod : forall m a n v, val_mem SEGS m a n v -> val_mem SEGS m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros m a n v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Z.mod_mod; [reflexivity|].
apply Z.pow_nonzero; lia.
Qed.
Lemma catd_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma catd_frame_HM : forall (W : world SEGS) mem m' sp,
(forall x : word, ~ (sp - 16 <= bv_unsigned x < sp) -> mrestrict (w_H W) m' x = mrestrict (w_H W) mem x) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (sp - REAC_BOX_CATALOGUE_DEFECT_STK <= a < sp) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) mem a.
Proof.
intros W mem m' sp HM a Ha Hn. apply catd_aview_eq. apply HM. rewrite unsigned_lit_small by lia.
unfold REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK in Hn. lia.
Qed.
Lemma catd_garr8_aview : forall (W : world SEGS) mem x l j, garr8 SEGS (mrestrict (w_H W) mem) x l -> (j < length l)%nat ->
aview SEGS (w_H W) mem (x + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W mem x l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)).
change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, YO0f.le_byte, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. repeat rewrite (Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis STRCMP : astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Lemma aj_strcmp_at : forall pc, astrcmp_realizes SEGS B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k (o : Z) raw,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall i, 0 <= i < k -> exists c, aview SEGS (w_H W) memT (x + i) = Some c /\ aview SEGS (w_H W) memT (y + i) = Some c /\ c <> 0) ->
(exists cx cy, aview SEGS (w_H W) memT (x + k) = Some cx /\ aview SEGS (w_H W) memT (y + k) = Some cy /\ (cx <> cy \/ cx = 0)) ->
src_ok SEGS W regsT memT x (k + 1) -> src_ok SEGS W regsT memT y (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) -> amem_range y (k + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview SEGS (w_H W) memT) x (k + 1) ->
range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview SEGS (w_H W) memT) y (k + 1) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> aview SEGS (w_H W) memT (x + k) = aview SEGS (w_H W) memT (y + k)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k o raw
HJ Ha0 Ha1 Hx0 Hy0 Hk0 Hk1 Hxk Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hpre Hend Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a) by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
destruct Hend as (cx & cy & Hvx & Hvy & Hne).
assert (Hmeet : AStrcmpDef.str_meet SEGS W memT x y k cx cy)
  by (unfold AStrcmpDef.str_meet; exact (conj Hk0 (conj Hpre (conj Hvx (conj Hvy Hne))))).
assert (Hres0 : w64 (AStrcmpDef.strcmp_res cx cy) = w64 0 <-> cx = cy).
{ unfold AStrcmpDef.strcmp_res. split.
  - destruct (Z.eqb_spec cx cy) as [E|E]; [intros _; exact E|].
    destruct (cx <? cy); intro Hw; exfalso; apply (f_equal bv_unsigned) in Hw; vm_compute in Hw; discriminate Hw.
  - intros E. subst cy. rewrite Z.eqb_refl. reflexivity. }
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y k cx cy HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hmeet Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
assert (Hcmp : w64 (AStrcmpDef.strcmp_res cx cy) = w64 0 <->
  aview SEGS (w_H W) memT (x + k) = aview SEGS (w_H W) memT (y + k)).
{ rewrite Hvx, Hvy. split.
  - intro Hw. apply Hres0 in Hw. subst cy. reflexivity.
  - intro Hs. injection Hs as Hs. apply Hres0. exact Hs. }
set (v := w64 (AStrcmpDef.strcmp_res cx cy)) in *.
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.
Lemma cd_entry : forall ly S W (regs : bvmap 5 word) mem md ch e P I O,
afn_pre SEGS B REAC_BOX_CATALOGUE_DEFECT_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> 0 <= P < 2 ^ 64 -> -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 ->
IMG_LO <= e + 8 -> e + 24 <= IMG_TOP -> catd_glob (e + 8) 16 -> e mod 8 = 0 ->
(e + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= e + 8) ->
(e + 24 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= e + 8) ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 8 P ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 4 I ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 O ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)))) ss_cd
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) mem (seg_rom SEGS))) /\
sh_ok SEGS CDBx cd_SH (Eimg (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch e P I O HPRE H10 Re RP RI RO Hlo Hhi Hg He8 Hs1 Hs31 M8 M16 M20.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_CATALOGUE_DEFECT_STK = 8208) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 31 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
pose proof (Z.mod_pos_bound I (2 ^ 32) ltac:(lia)) as RIu. pose proof (Z.mod_pos_bound O (2 ^ 32) ltac:(lia)) as ROu.
pose proof (pa_val_range (A_OBJ 1)) as V1. pose proof (pa_val_range (A_OBJ 31)) as V31.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32))) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 e) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (I mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (O mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB_CD) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (EO31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
destruct Hg as (q & z & Hqz & Hq1 & Hq2).
pose proof (ro_usable_glob SEGS B G ly S W mem md q z (e + 8) 16 GM Hqz HAR Hq1 Hq2) as HRA.
split.
- unfold ss_cd. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cd_regions, stack_region, got_regionP, bcell_regionP, cd_eregion.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
[cbn [sv_denot]; rewrite EO31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 CDBx SB_CD);
[cbn [sv_denot CDBx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_CD; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat e E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ e 8 8 _ P); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M8].
-- apply (chunk_ok_val SEGS E _ e 16 4 _ (I mod 2 ^ 32)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (catd_val_mem_mod _ _ 4 I M16).
-- apply (chunk_ok_val SEGS E _ e 20 4 _ (O mod 2 ^ 32)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (catd_val_mem_mod _ _ 4 O M20).
+ apply pairwise_disjoint_of_extents. unfold cd_regions, stack_region, got_regionP, bcell_regionP, cd_eregion, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat e E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by lia. rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) EO31) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR Hlo Hhi Hs1 Hs31. clear. intros.
repeat split; lia.
+ split; [|split; [exact Logic.I | exact Logic.I]].
cbn [cd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB_CD; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
unfold SB_CD. repeat match goal with |- _ /\ _ => split end; first [exact Hal16 | exact He8 | exact Logic.I | lia].
- unfold sh_ok, cd_SH. constructor; [|constructor].
eapply shent_ok_of_range; [exact HRA | | | | |].
+ unfold U, CDBx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB_CD; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma cd0_entry : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_BOX_CATALOGUE_DEFECT_STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_cd0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) mem (seg_rom SEGS))) /\
sh_ok SEGS CDBx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE. split; [|constructor].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_CATALOGUE_DEFECT_STK = 8208) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. unfold ss_cd0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
Qed.
Lemma catd_fin : forall E (s vu : Z), (s = 0 \/ s = 1) -> 0 <= vu < 2 ^ 64 -> ew E 40 = Z_to_bv 64 vu ->
U E (SAlu ALU_ADD (SAlu ALU_OR (SLit s) (SAlu ALU_SLL (SAlu ALU_SLTU (SLit 0) (SOff 40 0)) (SLit 1))) (SLit 0))
= s + (if vu =? 0 then 0 else 2).
Proof.
intros E s vu Hs Hv H40. rewrite !U_SAlu, !U_SLit, (U_atom E 40 vu H40 Hv). cbn [zalu_raw].
destruct (Z.eqb_spec vu 0) as [->|NZ].
- destruct Hs as [-> | ->]; vm_compute; reflexivity.
- replace (zcanon 0 <? vu) with true by (symmetry; apply Z.ltb_lt; unfold zcanon, M64; rewrite Z.mod_0_l by lia; lia).
destruct Hs as [-> | ->]; vm_compute; reflexivity.
Qed.
Lemma catd_bd_true : forall sP sd : list byte, sP = sd -> bool_decide (sP = sd) = true.
Proof.
intros sP sd H. unfold bool_decide.
match goal with |- (if ?D then _ else _) = _ => destruct D end; [reflexivity | contradiction].
Qed.
Lemma catd_bd_false : forall sP sd : list byte, sP <> sd -> bool_decide (sP = sd) = false.
Proof.
intros sP sd H. unfold bool_decide.
match goal with |- (if ?D then _ else _) = _ => destruct D end; [contradiction | reflexivity].
Qed.
Lemma catd_eqb32 : forall x y, -2 ^ 31 <= x < 2 ^ 31 -> -2 ^ 31 <= y < 2 ^ 31 -> (x mod 2 ^ 64 =? y mod 2 ^ 64) = (x =? y).
Proof.
intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|].
apply Z.eqb_neq. intros Hm. apply NE. Z.div_mod_to_equations. lia.
Qed.
Local Ltac cd_upd regs Usp :=
match goal with
| HF : frame_of ?Ex ?rs ?m1 ?m2, HM : forall x : word, _ -> ?m1 x = ?m0 x |- _ =>
let HM' := fresh "HM" in
assert (HM' : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> m2 x = m0 x)
by (intros x Hx; transitivity (m1 x); [ apply HF; let rs' := eval vm_compute in rs in change rs with rs';
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); apply Hx; cbn [In] in Hin;
repeat destruct Hin as [<- | Hin]; try contradiction;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?Usp in Hr;
first [lia | let t := type of Hr in idtac "HRFAIL" t; fail]
| exact (HM x Hx) ]);
clear HM HF; rename HM' into HM
| |- _ => idtac "CDUPD-NOMATCH"; match goal with H : frame_of _ _ _ _ |- _ => let t := type of H in idtac "F" t end;
match goal with H : forall x : word, _ |- _ => let t := type of H in idtac "M" t end; fail
end.
Theorem pb_reac_box_catalogue_defect : treac_box_catalogue_defect_spec.
Proof.
unfold treac_box_catalogue_defect_spec.
intros ly S W regs mem md ch e i o d I O P sP sd HPRE H10 H11 H12 H13 Re Ri Ro Rd RI RO RP HROW HSTR.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
pose proof (ajournal_init SEGS B REAC_BOX_CATALOGUE_DEFECT_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_CATALOGUE_DEFECT_STK = 8208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at, A_reac_box_catalogue_defectP.
change (w64 (BASE + AF_reac_box_catalogue_defect)) with (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)).
destruct (Z.eq_dec e 0) as [E0 | E0].
- subst e. clear HROW HSTR.
destruct (cd0_entry ly S W regs mem md ch HPRE) as [HS SHOK].
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (HM : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mrestrict (w_H W) mem x = mrestrict (w_H W) mem x)
by (intros; reflexivity).
paj_run_tok RUN HS HJ SHOK CDBspan; [awr_ok_tac; exact Usp |].
repeat match goal with H : mem_grows _ _ |- _ => clear H end.
cd_upd regs Usp.
psrr_branch_tok RUN BR HS SHOK CDBspan.
+ paj_run_tok RUN HS HJ SHOK CDBspan; [awr_ok_tac; exact Usp |].
repeat match goal with H : mem_grows _ _ |- _ => clear H end.
cd_upd regs Usp.
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_box_catalogue_defect_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10; reflexivity|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
exact (catd_frame_HM W mem (ms_mem msc) (spZ regs) HM)
end.
+ exfalso. rewrite branch_eq_U, (U_atom E 10 0 E10), U_lit in Hc by lia. discriminate Hc.
- destruct (HROW E0) as (Hlo & Hhi & Hg & He8 & Hs1 & Hs31 & M8 & M16 & M20). clear HROW.
destruct (cd_entry ly S W regs mem md ch e P I O HPRE H10 Re RP RI RO Hlo Hhi Hg He8 Hs1 Hs31 M8 M16 M20) as [HS SHOK].
remember (Eimg (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32))) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 o) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (I mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (O mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (HAE : env_agree 32 (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32))) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EL.
assert (HM : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mrestrict (w_H W) mem x = mrestrict (w_H W) mem x)
by (intros; reflexivity).
let rec go :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok RUN HS HJ SHOK CDBspan; [awr_ok_tac; exact Usp |];
repeat match goal with H : mem_grows _ _ |- _ => clear H end;
cd_upd regs Usp;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => idtac
| HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ _ _ _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM CDBx cd_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K CDBx CDBspan cd_SH (start K CDBx CDBspan cd_SH ss) end in
lazymatch why with
| SR_jalr _ => idtac
| SR_branch _ _ _ => psrr_branch_tok RUN BR HS' SHOK' CDBspan; [go | go]
| _ => let pc := eval vm_compute in (ss_pc ss) in idtac "STUCK" pc why; fail
end
end end in go.
all: repeat match goal with
| H : branch_taken _ (sv_denot ?Ex _) (sv_denot ?Ex _) = _ |- _ =>
let X11 := fresh "X" in let X12 := fresh "X" in let X13 := fresh "X" in
let X32 := fresh "X" in let X33 := fresh "X" in let X34 := fresh "X" in
assert (X11 : ew Ex 11 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E11);
assert (X12 : ew Ex 12 = Z_to_bv 64 o) by (cbn [ew ewset Nat.eqb]; exact E12);
assert (X13 : ew Ex 13 = Z_to_bv 64 d) by (cbn [ew ewset Nat.eqb]; exact E13);
assert (X32 : ew Ex 32 = Z_to_bv 64 P) by (cbn [ew ewset Nat.eqb]; exact E32);
assert (X33 : ew Ex 33 = Z_to_bv 64 (I mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E33);
assert (X34 : ew Ex 34 = Z_to_bv 64 (O mod 2 ^ 32)) by (cbn [ew ewset Nat.eqb]; exact E34);
rewrite ?branch_ne_U, ?branch_eq_U in H;
rewrite ?(catd_sext Ex 33 I X33 RI), ?(catd_sext Ex 34 O X34 RO), ?(catd_U_atom_mod Ex 11 i X11), ?(catd_U_atom_mod Ex 12 o X12),
?(U_atom Ex 13 d X13 Rd), ?(U_atom Ex 32 P X32 RP), ?(U_lit Ex 0 ltac:(lia)) in H;
rewrite ?(catd_eqb32 I i RI Ri), ?(catd_eqb32 O o RO Ro) in H;
rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in H;
clear X11 X12 X13 X32 X33 X34
end.
all: lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) _ |- _ => idtac
| HS : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msc) |- _ =>
prreg HS (1%bv : bv 5) R1; prreg HS (10%bv : bv 5) R10;
assert (HAEx : env_agree 32 (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32))) Ex)
by (split; [ intros n Hn; rewrite <- (proj1 HAE n Hn); cbn [ew ewset];
repeat match goal with |- context [Nat.eqb n ?k] => let h := fresh in destruct (Nat.eqb_spec n k) as [h|h]; [exfalso; lia|] end; reflexivity
| cbn [ed ewset]; exact (proj2 HAE) ]);
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_box_catalogue_defect_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ex _ _ regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)) HS); [exact HAEx | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10;
unfold w64, reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK;
replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0);
repeat match goal with H : (?x =? ?y) = ?b |- context [?x =? ?y] => rewrite H end;
cbn [andb orb]; reflexivity |];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
exact (catd_frame_HM W mem (ms_mem msc) (spZ regs) HM)
end.
all: lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msX), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mT ?mdT _ |- _ =>
let Dnz := fresh "Dnz" in let Pnz := fresh "Pnz" in
pose proof (proj1 (Z.eqb_neq d 0) ltac:(assumption)) as Dnz;
pose proof (proj1 (Z.eqb_neq P 0) ltac:(assumption)) as Pnz;
destruct (HSTR E0 Dnz Pnz) as ((GP & NP & (qP & zP & HqP & HqP1 & HqP2) & LoP & HiP) & (GD & ND & (nd & Hind & Lnd)));
pmkst HS;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (1%bv : bv 5) Rra;
prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
assert (A10 : getr (ms_regs msX) 10 = w64 P) by (rewrite Ra0; exact E32);
assert (A11 : getr (ms_regs msX) 11 = w64 d) by (rewrite Ra1; exact E13);
assert (Asp : spZ (ms_regs msX) = spZ regs + -16) by (unfold spZ at 1; rewrite Rsp, Usp, unsigned_lit_small by lia; reflexivity);
assert (Agp : getr (ms_regs msX) 3 = w64 (as_gp B)) by (rewrite Rgp, E3; exact Hgp);
assert (Atp : getr (ms_regs msX) 4 = w64 (as_tp B)) by (rewrite Rtp, E4; exact Htp);
destruct (catd_k_le sP sd) as [KP KD];
destruct (catd_k_spec sP sd NP ND) as (KS1 & KS2 & KS3);
pose proof (proj1 HJ) as HART;
destruct (al_blocks _ _ LAWS ly S W mem md d nd HAR Hind) as (Hd16 & Hd4096 & Hdceil & Hdia & Hdpres & _);
assert (Rnd : req_size nd = nd) by (unfold req_size; destruct (Z.eqb_spec nd 0); lia);
rewrite Rnd in Hdceil;
assert (AVP : forall j, (j <= length sP)%nat -> aview SEGS (w_H W) mT (P + Z.of_nat j) = Some (nth j (catd_lz sP) 0))
by (intros j Hj; rewrite (catd_aview_eq (w_H W) mem mT (P + Z.of_nat j));
[ apply catd_garr8_aview; [exact GP | rewrite catd_lz_len; lia]
| apply HM; rewrite unsigned_lit_small by lia; lia ]);
assert (AVD : forall j, (j <= length sd)%nat -> aview SEGS (w_H W) mT (d + Z.of_nat j) = Some (nth j (catd_lz sd) 0))
by (intros j Hj; rewrite (catd_aview_eq (w_H W) mem mT (d + Z.of_nat j));
[ apply catd_garr8_aview; [exact GD | rewrite catd_lz_len; lia]
| apply HM; rewrite unsigned_lit_small by lia; lia ]);
set (kk := catd_k sP sd) in *;
assert (KPRE : forall i0, 0 <= i0 < Z.of_nat kk -> exists c, aview SEGS (w_H W) mT (P + i0) = Some c /\ aview SEGS (w_H W) mT (d + i0) = Some c /\ c <> 0)
by (intros i0 Hi0; destruct (KS1 (Z.to_nat i0) ltac:(lia)) as [Eq Nz]; exists (nth (Z.to_nat i0) (catd_lz sP) 0);
replace (P + i0) with (P + Z.of_nat (Z.to_nat i0)) by lia; replace (d + i0) with (d + Z.of_nat (Z.to_nat i0)) by lia;
split; [apply AVP; lia|]; split; [rewrite Eq; apply AVD; lia | exact Nz]);
assert (KAT : exists cx cy, aview SEGS (w_H W) mT (P + Z.of_nat kk) = Some cx /\ aview SEGS (w_H W) mT (d + Z.of_nat kk) = Some cy /\ (cx <> cy \/ cx = 0))
by (exists (nth kk (catd_lz sP) 0), (nth kk (catd_lz sd) 0); split; [apply AVP; lia|]; split; [apply AVD; lia | exact KS2]);
assert (SRCP : src_ok SEGS W (ms_regs msX) mT P (Z.of_nat kk + 1))
by (intros a Ha; split; [replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia; rewrite AVP by lia; discriminate | rewrite Asp, Hes; lia]);
assert (SRCD : src_ok SEGS W (ms_regs msX) mT d (Z.of_nat kk + 1))
by (intros a Ha; split; [replace a with (d + Z.of_nat (Z.to_nat (a - d))) by lia; rewrite AVD by lia; discriminate | rewrite Asp, Hes; lia]);
destruct (ro_read_ok_glob SEGS B G ly S W mT mdT qP zP P (Z.of_nat kk + 1) GM HqP IV HART ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)) as [RAP HULLP];
pose proof (range_addressable_of_block SEGS B LAWS ly S W mT mdT d nd d (Z.of_nat kk + 1) HART Hind ltac:(lia) ltac:(rewrite Rnd; lia)) as RAD;
pose proof (shadow_hull_vis_of_block SEGS B LAWS ly S W mT mdT d nd d (Z.of_nat kk + 1) HART Hind ltac:(lia) ltac:(rewrite Rnd; lia) ltac:(lia)) as HULLD;
pose proof (amem_range_of_block SEGS B LAWS ly S W mem md d nd d (Z.of_nat kk + 1) HAR Hind ltac:(lia) ltac:(rewrite Rnd; lia)) as AMD;
assert (AMP : amem_range P (Z.of_nat kk + 1)) by (unfold amem_range; left; rewrite C5; lia);
eapply SRr_bind;
[ eapply (aj_strcmp_at _ STRCMP W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P d (Z.of_nat kk) (-16) _);
[ exact HJ | exact A10 | exact A11 | lia | lia | lia | lia | lia | lia | exact Asp | reflexivity | lia | rewrite WS, Hes; lia
| exact Agp | exact Atp | exact Rra | apply ret_ok_codeptr_v; [lia | reflexivity]
| exact KPRE | exact KAT | exact SRCP | exact SRCD
| intros a Ha; rewrite Hes; lia | intros a Ha; rewrite Hes; lia
| exact AMP | exact AMD | exact RAP | exact HULLP | exact RAD | exact HULLD ]
| ];
cbv beta;
let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in
let md2 := fresh "md2" in let v := fresh "v" in let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in
let Hv := fresh "Hv" in let Hcmp := fresh "Hcmp" in let Hfr := fresh "Hfr" in let Hpres2 := fresh "Hpres2" in
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpres2);
let HJpres := fresh "HJpres" in
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _);
let HAEx := fresh "HAEx" in
assert (HAEx : env_agree 32 (Ereg regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32))) Ex)
by (split; [ intros n Hn; rewrite <- (proj1 HAE n Hn); cbn [ew ewset];
repeat match goal with |- context [Nat.eqb n ?k] => let h := fresh in destruct (Nat.eqb_spec n k) as [h|h]; [exfalso; lia|] end; reflexivity
| cbn [ed ewset]; exact (proj2 HAE) ]);
let HS2 := fresh "HS2" in
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
match type of HS2 with ?tq -> _ =>
let HRK := fresh "HRK" in
assert (HRK : tq);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; cbn [ew ewset Nat.eqb]; rewrite Usp; intros a Ha;
[ apply (mbyte_of_aview SEGS); apply Hfr; [lia | rewrite Hes; lia]
| intros _; apply (apresent_writable SEGS); apply HJpres; lia ]
| specialize (HS2 HRK); clear HRK ]
end;
clear HS; rewrite <- restrict_mkst_fx in HS2;
let E' := fresh "E'" in let HE' := fresh "HE'" in
remember (havoc Ex 36 (map (getr regs2) CLOB)) as E' eqn:HE' in HS2;
let HEI' := fresh "HEI'" in
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [assumption | cbv; lia]);
let HAE' := fresh "HAE'" in
pose proof (env_agree_havoc_ge 32 36 _ Ex (map (getr regs2) CLOB) ltac:(lia) HAEx) as HAE';
rewrite <- HE' in HAE';
let F1 := fresh "F1" in let Usp' := fresh "Usp'" in
assert (F1 : ew E' 1 = getr regs 1) by (rewrite (proj1 HAE' 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl));
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite (proj1 HAE' 2%nat ltac:(lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity);
let V40 := fresh "V40" in
assert (V40 : ew E' 40 = getr regs2 10) by (rewrite HE'; reflexivity);
clear HE';
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss3 _ => let vv := eval vm_compute in ss3 in change ss3 with vv in HS2 end;
let SHOK' := fresh "SHOK'" in
assert (SHOK' : sh_ok SEGS CDBx [] E' (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil);
paj_run_tok RUN HS2 HJ2 SHOK' CDBspan; [awr_ok_tac; exact Usp' |];
repeat match goal with H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with HF : frame_of _ _ ?m1 _ |- _ =>
assert (HMc : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> m1 x = m1 x) by (intros; reflexivity) end;
cd_upd regs Usp';
let CMP := fresh "CMP" in
assert (CMP : bv_unsigned v = 0 <-> sP = sd)
by (rewrite <- KS3; rewrite (AVP kk ltac:(lia)), (AVD kk ltac:(lia)) in Hcmp; split;
[ let H0 := fresh in let Hv0 := fresh in intros H0;
assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity);
apply Hcmp in Hv0; injection Hv0 as Hv0; exact Hv0
| let H0 := fresh in let Hv0 := fresh in intros H0;
assert (Hv0 : v = w64 0) by (apply Hcmp; rewrite H0; reflexivity);
rewrite Hv0; reflexivity ]);
let V40' := fresh "V40'" in
assert (V40' : ew E' 40 = Z_to_bv 64 (bv_unsigned v)) by (rewrite V40, Hv, Z_to_bv_bv_unsigned; reflexivity);
pose proof (bv_unsigned_in_range 64 v) as Rv; change (bv_modulus 64) with (2 ^ 64) in Rv;
lazymatch goal with HS3 : st_ok_pi _ _ ?Ey ?ssx (restrict _ ?msc) |- _ =>
prreg HS3 (1%bv : bv 5) R1;
pose proof (st_ok_pi_restrict_reg _ Ey ssx msc (10%bv : bv 5) HS3) as R10;
let e10 := eval vm_compute in (sr_get (ss_regs ssx) (10%bv : bv 5)) in change (sr_get (ss_regs ssx) (10%bv : bv 5)) with e10 in R10;
eapply (RET W _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_box_catalogue_defect_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, F1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ Ey _ _ regs (cd_extra P (I mod 2 ^ 32) (O mod 2 ^ 32)) HS3); [exact HAE' | vm_compute; reflexivity]|];
split; [cbn [ms_regs restrict] in R10 |- *; rewrite R10, denot_lit_U; unfold w64; f_equal;
lazymatch goal with |- context [SAlu ALU_OR (SLit ?s0) _] => rewrite (catd_fin Ey s0 (bv_unsigned v) ltac:(lia) Rv V40') end;
unfold reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK;
replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0);
repeat match goal with H : (?x =? ?y) = ?b |- context [?x =? ?y] => rewrite H end;
destruct (Z.eq_dec (bv_unsigned v) 0) as [V0 | V0];
[ rewrite (catd_bd_true sP sd (proj1 CMP V0)), V0
| rewrite (catd_bd_false sP sd (fun Q => V0 (proj2 CMP Q))), (proj2 (Z.eqb_neq _ _) V0) ];
cbn [andb orb]; reflexivity |];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [apply Permutation_refl|];
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn;
transitivity (aview SEGS (w_H W) mem2 a); [exact (catd_frame_HM W mem2 (ms_mem msc) (spZ regs) HMc a Ha Hn)|];
transitivity (aview SEGS (w_H W) mT a);
[ apply Hfr; [exact Ha | clear - Hn Hes; unfold REAC_BOX_CATALOGUE_DEFECT_STK in Hn; rewrite Hes in *; lia] |];
exact (catd_frame_HM W mem mT (spZ regs) HM a Ha Hn)
end
end.
Qed.
End h.
End f.
End d.
