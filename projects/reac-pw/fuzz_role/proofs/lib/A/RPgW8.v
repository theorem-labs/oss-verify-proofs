From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW8Kit RPgW8BlkA RPgW8BlkB RPgW8Rok RPgW8BlkC1 RPgW8BlkC0D RPgW8Call RPgW8Geo RPgW8Img RPgW8Fin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Arguments x_STK {segs} r. #[local] Arguments x_sp0 {segs} r. #[local] Arguments x_FP {segs} r.
#[local] Arguments x_ly {segs} r. #[local] Arguments x_S {segs} r. #[local] Arguments x_W0 {segs} r.
#[local] Arguments x_mem0 {segs} r. #[local] Arguments x_md0 {segs} r. #[local] Arguments x_own {segs} r.
#[local] Arguments x_k {segs} r. #[local] Arguments x_regs {segs} r. #[local] Arguments x_lyc {segs} r.
#[local] Arguments x_Sc {segs} r. #[local] Arguments x_W {segs} r. #[local] Arguments x_memc {segs} r.
#[local] Arguments x_mdc {segs} r. #[local] Arguments x_RLO {segs} r. #[local] Arguments x_RHI {segs} r.
#[local] Arguments x_e {segs} r. #[local] Arguments x_pos {segs} r.

(* ============================== bytes a step leaves alone ============================== *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition wun (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview rsegs H m' a = aview rsegs H m a.
Lemma wun_trans : forall H m1 m2 m3 (P Q : Z -> Prop), wun H m1 m2 P -> wun H m2 m3 Q -> wun H m1 m3 (fun a => P a \/ Q a).
Proof. intros H m1 m2 m3 P Q H1 H2 a Ha Hn. rewrite (H2 a Ha) by tauto. apply H1; tauto. Qed.
Lemma wun_mono : forall H m m' (P Q : Z -> Prop), wun H m m' P -> (forall a, 0 <= a < 2 ^ 64 -> P a -> Q a) -> wun H m m' Q.
Proof. intros H m m' P Q HP HPQ a Ha Hn. apply HP; [exact Ha|]. intros Hp. exact (Hn (HPQ a Ha Hp)). Qed.
Lemma wun_val : forall H m m' (P : Z -> Prop) a n v, wun H m m' P -> val_mem rsegs (mrestrict H m) a n v ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ P x) -> val_mem rsegs (mrestrict H m') a n v.
Proof.
intros H m m' P a n v HU V H0 H1 HP kk Hk. rewrite (mbyte_of_aview rsegs H H m m' (a + Z.of_nat kk)); [exact (V kk Hk)|].
apply HU; [lia | apply HP; lia].
Qed.
Lemma wun_bytes : forall H m m' (P : Z -> Prop) a l, wun H m m' P -> rm_bytes rsegs H m a l ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat (length l) -> ~ P x) -> rm_bytes rsegs H m' a l.
Proof. intros H m m' P a l HU HB H0 H1 HP. apply (rm_bytes_kept rsegs H m H m' a l HB). intros x Hx. apply HU; [lia | apply HP; lia]. Qed.
Lemma wun_fsh : forall H m m' (P : Z -> Prop) F pat, wun H m m' P -> rl_fsh rsegs H m F pat ->
  0 <= shadow_addr F -> shadow_addr F + Z.of_nat (length pat) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length pat) -> ~ P (shadow_addr F + i)) -> rl_fsh rsegs H m' F pat.
Proof. intros H m m' P F pat HU HF H0 H1 HP. apply (rm_fsh_kept rsegs H m H m' F pat HF). intros i Hi. apply HU; [lia | apply HP; lia]. Qed.
Lemma wun_slots : forall H m m' (P : Z -> Prop) R l, wun H m m' P ->
  Forall (fun c => val_mem rsegs (mrestrict H m) (R + fst c) 8 (snd c mod 2 ^ 64)) l ->
  (forall c, In c l -> 0 <= R + fst c /\ R + fst c + 8 <= 2 ^ 64 /\ forall x, R + fst c <= x < R + fst c + 8 -> ~ P x) ->
  Forall (fun c => val_mem rsegs (mrestrict H m') (R + fst c) 8 (snd c mod 2 ^ 64)) l.
Proof.
intros H m m' P R l HU HL HP. rewrite Forall_forall in *. intros c Hc. destruct (HP c Hc) as (H0 & H1 & H2).
apply (wun_val H m m' P); [exact HU | exact (HL c Hc) | exact H0 | exact H1 | exact H2].
Qed.
Lemma wpres_bv : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hr. Qed.
Lemma wkeep_saved : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r wkeep -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
cbv [wkeep In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<-|Hr];
  [match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia|]).
destruct Hr.
Qed.
Lemma w_ret_B : YK0s.ret_ok (Z_to_bv 64 0x817a4).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w_ret_C : YK0s.ret_ok (Z_to_bv 64 0x817f0).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w_ret_D : YK0s.ret_ok (Z_to_bv 64 0x81850).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma w_enc_bytes : forall H m a (s t : Z) body pd,
  rm_bytes rsegs H m a (le32 s) -> rm_bytes rsegs H m (a + 4) (le32 t) -> rm_bytes rsegs H m (a + 8) body ->
  rm_bytes rsegs H m (a + 8 + Z.of_nat (length body)) (zeros pd) ->
  rm_bytes rsegs H m a (le32 s ++ le32 t ++ body ++ zeros pd).
Proof.
intros H m a s t body pd H1 H2 H3 H4. apply (proj2 (rm_bytes_app rsegs H m a _ _)). split; [exact H1|].
rewrite length_le32. change (Z.of_nat 4) with 4.
apply (proj2 (rm_bytes_app rsegs H m _ _ _)). split; [exact H2|]. rewrite length_le32. change (Z.of_nat 4) with 4.
replace (a + 4 + 4) with (a + 8) by ring.
apply (proj2 (rm_bytes_app rsegs H m _ _ _)). split; [exact H3 | exact H4].
Qed.
Lemma w_body_of : forall H m F ed, rm_bytes rsegs H m (F + 0xf0) (ent_mem ed) -> rm_bytes rsegs H m (F + 0xf8) (e_body ed).
Proof.
intros H m F ed HE. unfold ent_mem in HE.
apply (proj1 (rm_bytes_app rsegs H m _ _ _)) in HE as [_ HE]. rewrite length_le32 in HE.
apply (proj1 (rm_bytes_app rsegs H m _ _ _)) in HE as [_ HE]. rewrite length_le32 in HE.
apply (proj1 (rm_bytes_app rsegs H m _ _ _)) in HE as [HE _].
replace (F + 0xf8) with (F + 0xf0 + Z.of_nat 4 + Z.of_nat 4) by (cbn; ring). exact HE.
Qed.
(* W8img.wi_final in the shapes the assembly has at hand *)
Lemma wi_loc : forall H m2 m3 pp sh ps es ed L sz pad kk,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> ent_wf ed ->
  (length ps <= 2)%nat -> (length es < 32)%nat -> 0 <= pp -> pp + 19744 <= 2 ^ 64 ->
  L = Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) -> sz = e_size ed -> pad = pad8 (e_size ed) ->
  kk = Z.of_nat (length es) ->
  rm_bytes rsegs H m2 pp (pc_image (PbCut sh ps (Some es))) ->
  rm_bytes rsegs H m3 (pp + L) (enc_pod ed) ->
  val_mem rsegs (mrestrict H m3) (pp + 0x4000) 8 (L + 8 + sz + pad) ->
  (pc_first (PbCut sh ps (Some es)) = true ->
     val_mem rsegs (mrestrict H m3) (pp + 0x4d14) 4 (kk + 1) /\
     rm_bytes rsegs H m3 (pp + 0x4014 + 104 * kk) (ent_mem ed)) ->
  (forall a, pp <= a < pp + 19744 -> ~ (pp + L <= a < pp + L + 8 + sz + pad) -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) ->
     (pc_first (PbCut sh ps (Some es)) = true ->
        ~ (pp + 0x4d14 <= a < pp + 0x4d14 + 4) /\ ~ (pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104)) ->
     aview rsegs H m3 a = aview rsegs H m2 a) ->
  rm_bytes rsegs H m3 pp (pc_image (PbCut sh ps (Some (es ++ [ed])))).
Proof.
intros H m2 m3 pp sh ps es ed L sz pad kk HPV HPE HES Hwf Hps Hes H0 H1 EL Esz Epad Ekk HI HE HL HF HU.
pose proof (wi_final H m2 m3 pp sh ps es ed HPV HPE HES Hwf Hps Hes H0 ltac:(unfold Layout.PP_SIZE; lia)) as WI.
cbv zeta in WI. subst L sz pad kk. apply WI; clear WI.
- exact HI.
- exact HE.
- exact HL.
- intros Hf. destruct (HF Hf) as [A1 A2]. split; [exact A1|].
  replace (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (length es))) with (pp + 0x4014 + 104 * Z.of_nat (length es))
    by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; ring). exact A2.
- intros a Ha A1 A2 A3. unfold Layout.PP_SIZE, Layout.OFF_LEN, Layout.OFF_N_ENT, Layout.OFF_ENT, Layout.ENT_SIZE in *.
  apply HU; [lia | lia | lia |]. intros Hf. destruct (A3 Hf) as [A4 A5]. split; lia.
Qed.
End u.

Ltac wkeep_in := unfold wkeep; repeat (first [left; reflexivity | right]).
Ltac wcs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
(* the kernel's contracts of __asan_memcpy and __asan_memset (YG0d.aintrin_realizes) at image A's entries *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy 0x510d4.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x51570.

Lemma w_fsh_awr : forall STK sp0 FP bl0 blc ly own pos F, In (3, pos) own -> frame_addr ly 3 pos = F ->
  forall a, shadow_addr F + 30 <= a < shadow_addr F + 43 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos F Hown HF a Ha. right; right; right. exists 3, pos. split; [exact Hown|].
right. unfold in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3 / 8) with 64. lia.
Qed.

Lemma rs_PJ_e : rs_PJ = rm_sh false false false true false.
Proof. vm_compute. reflexivity. Qed.

Theorem rs_piece_W8 : rs_piece_W8_stmt rsegs B MT.
Proof.
intros cx POST rest i k HST HFC HFCL ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed Hi Hk HJ.
pose proof HST as HST0. pose proof HJ as HJcut.
pose proof (w8_J_facts B MT cx rest sh np ps cnt es rr r ed ly2 S2 W2 regs2 mem2 md2 HST HJ) as HFX. cbv zeta in HFX.
destruct HFX as (HJ2 & Hpp2 & Hfr & Hfin & HFa & R2 & R3 & R4 & R9 & R19 & R20 & R21 & R23 & R27 & HSL & HEM & HTY & HSZ &
  HIMG & HLEN & HNE & HFSH & Hpp16 & Happ & Hpphi & HF32 & HFapp & HFhi & HpF & HRc & HR16 & HRS & Hsp16 & Hsp47 & HSTK &
  HL & HL8 & Hwf & Hes32 & Hescnt & Hcnt & Hfs01 & Hfs & HPV & HPE & HES & Hps2).
destruct HST as (HP & _ & _ & _). pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & _).
change (hi_cid role_himg_A) with 3 in Hown.
pose proof Hwf as (Hty & Hbody & Hsz).
pose proof (Model.pad8_bound (e_size ed)) as Hpad.
pose proof YM05.alloc_ceiling_val as (Hc1 & _).
destruct (wpp_zone (e_pp (x_e cx)) Hpp16 Happ Hpphi) as (Hpp4096 & Hshp1 & Hshp2 & Hzpp).
destruct (wF_zone (e_F (x_e cx)) HF32 HFapp HFhi) as (HF4096 & HsF1 & HsF2 & HzF & HF8d & HsFd).
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *. set (pp := e_pp (x_e cx)) in *.
set (sF := shadow_addr F) in *.
set (L := Z.of_nat (length (pc_buf (PbCut sh ps (Some es))))) in *.
set (sz := e_size ed) in *. set (ty := e_type ed) in *. set (fs := rs_first ps) in *. set (kk := Z.of_nat (length es)) in *.
set (sp0 := x_sp0 cx) in *. set (STK := x_STK cx) in *.
unfold T_SEG_STK, ASTACK in HRc, HSTK.
assert (HF8 : F mod 8 = 0) by (apply wmod16_8; apply Z.mod_divide in HF32; [|lia]; destruct HF32 as [q ->];
  replace (q * 32) with ((2 * q) * 16) by lia; apply Z_mod_mult).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (HsppF : pp + 19744 <= sF \/ sF + 64 <= pp) by (destruct Hzpp; lia).
assert (HshFpp : sF + 64 <= shadow_addr pp \/ shadow_addr pp + 2468 <= sF).
{ assert (Hsh_pp : shadow_addr pp = 0x7fff8000 + pp / 8) by reflexivity.
  assert (HppD : pp = 8 * (pp / 8)) by (pose proof (Z.div_mod pp 8 ltac:(lia)); lia).
  destruct HpF as [H1|H1]; [right | left]; lia. }
assert (Hspo : sp0 + (R - sp0) = R) by ring.
(* ------------------------------ A: 0x8165c -> the body's memcpy ------------------------------ *)
destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJ2 Hpp2 Hfin HFa) as (N2sh & N2pp & N2F & N2Fs & N2ra & N2hl).
eapply SRr_bind.
{ apply (w_blkA B STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 regs2 mem2 md2
    (x_k cx) R F pp L ty sz fs kk cnt HJ2 Hpp2 Hfr R9 R20 R21 R23 R27 HSL HTY HSZ HLEN N2sh N2pp Hpp16 Happ HFapp HpF
    Hpphi HFhi); try lia; destruct Hfs01 as [-> | ->]; lia. }
intros W' c' _ (-> & regsA & memA & mdA & -> & HJA & HioA & A1 & A10 & A11 & A12 & A24 & AK & AL & Asz & Aty & AU).
destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJA Hpp2 Hfin HFa) as (NAsh & NApp & NAF & NAFs & NAra & NAhl).
assert (UA : wun (w_H W2) mem2 memA (fun a => pp + L <= a < pp + L + 8 \/ pp + 0x4000 <= a < pp + 0x4000 + 8))
  by (intros a Ha Hn; apply AU; [exact Ha | tauto | tauto]).
assert (HFSHA : rl_fsh rsegs (w_H W2) memA F rs_PJ).
{ apply (wun_fsh _ _ _ _ F rs_PJ UA HFSH); [lia | change (Z.of_nat (length rs_PJ)) with 52; lia |].
  change (Z.of_nat (length rs_PJ)) with 52. intros j Hj. destruct HsppF; lia. }
assert (Hlem : Z.of_nat (length (ent_mem ed)) = 104).
{ rewrite length_ent_mem; [reflexivity|]. rewrite Hbody. lia. }
assert (HEMA : rm_bytes rsegs (w_H W2) memA (F + 0xf0) (ent_mem ed)).
{ apply (wun_bytes _ _ _ _ _ _ UA HEM); rewrite ?Hlem; try lia; intros x Hx; destruct HpF; lia. }
(* ------------------------------ M1: __asan_memcpy(pp + L + 8, &e.body, size) ------------------------------ *)
assert (AR2 : getr regsA 2 = w64 R) by (rewrite (AK 2%bv ltac:(wkeep_in)); exact R2).
assert (AR3 : getr regsA 3 = w64 (as_gp B)) by (rewrite (AK 3%bv ltac:(wkeep_in)); exact R3).
assert (AR4 : getr regsA 4 = w64 (as_tp B)) by (rewrite (AK 4%bv ltac:(wkeep_in)); exact R4).
assert (HspA : spZ regsA = sp0 + (R - sp0)) by (unfold spZ; rewrite AR2, Hspo; apply unsigned_lit_small; lia).
assert (Ho16 : (R - sp0) mod 16 = 0) by (rewrite Zminus_mod, HR16, Hsp16; reflexivity).
assert (HappL : forall d n, pp <= d -> d + n <= pp + 19744 -> 0 <= n -> amem_range d n).
{ intros d n H1 H2 H3. pose proof ASAN_CEIL_range as ((Ha1 & Ha2) & _). unfold in_app in Happ.
  destruct Happ as (_ & [Hz | (Hz1 & Hz2)]); unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg in *;
  [left | right]; lia. }
assert (HappF : forall d n, F <= d -> d + n <= F + 512 -> 0 <= n -> amem_range d n).
{ intros d n H1 H2 H3. pose proof ASAN_CEIL_range as ((Ha1 & Ha2) & _). unfold in_app in HFapp.
  destruct HFapp as (_ & [Hz | (Hz1 & Hz2)]); unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg in *;
  [left | right]; lia. }
assert (Hawpp : forall a, pp <= a < pp + 19744 ->
  awr_byte STK sp0 (x_FP cx) (ablocks B (x_ly cx) (x_S cx)) (ablocks B ly2 S2) ly2 (x_own cx) a).
{ intros a Ha. replace a with (pp + (a - pp)) by lia.
  apply (rl_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hpp2 | exact Hfr | unfold req_size, Layout.PP_SIZE; cbn; lia]. }
assert (HFSHAe := HFSHA). rewrite rs_PJ_e in HFSHAe.
eapply SRr_bind.
{ apply (w_intrin_at B OCpy 0x510d4 AMEMCPY W2 regsA memA STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 mdA (x_k cx) (pp + L + 8) (F + 0xf8) sz (R - sp0) (getr regsA 1) HJA A10 A11 A12).
  - lia.
  - lia.
  - lia.
  - exact HspA.
  - exact Ho16.
  - lia.
  - unfold ESTACK; lia.
  - exact AR3.
  - exact AR4.
  - reflexivity.
  - rewrite A1. exact w_ret_B.
  - intros a Ha. split; [apply Hawpp; lia | unfold ESTACK; lia].
  - apply HappL; lia.
  - apply (NAra (pp + L + 8) sz); lia.
  - intros Hn. apply (NAra (pp + L + 8) sz); lia.
  - cbn iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [apply (aview_some_of_apresent rsegs); replace a with (F + (a - F)) by lia; apply NAF; lia
      | rewrite HspA; unfold ESTACK; lia]. }
    split; [destruct HpF; [left | right]; lia|]. split; [apply HappF; lia|]. split.
    { pose proof (rm_A_ra_e rsegs _ _ F false false false false 8 sz HFSHAe HF8 ltac:(lia) ltac:(lia)) as Hra.
      unfold RM_E in Hra. replace (F + 0xf8) with (F + 0xf0 + 8) by lia. exact Hra. }
    intros Hn. apply NAhl; lia. }
intros W' c' _ (-> & regsB & memB & mdB & -> & HJB & HioB & HPB & B10 & Bcpy & BU & Bpres).
assert (UB : wun (w_H W2) memA memB (fun a => pp + L + 8 <= a < pp + L + 8 + sz \/ R - ESTACK <= a < R)).
{ intros a Ha Hn. apply BU; [exact Ha | intros Hx; apply Hn; left; lia | intros Hx; apply Hn; right; lia]. }
destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJB Hpp2 Hfin HFa) as (NBsh & NBpp & NBF & NBFs & NBra & NBhl).
(* ------------------------------ B: 0x817a4 -> the pad's memset ------------------------------ *)
assert (BK : forall r : bv 5, In r wkeep -> getr regsB r = getr regs2 r).
{ intros r0 Hr0. rewrite (wkeep_saved _ _ HPB r0 Hr0). exact (AK r0 Hr0). }
rewrite A1. eapply SRr_bind.
{ apply (w_blkB B STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 regsB memB mdB
    (x_k cx) pp L sz HJB Hpp2 Hfr).
  - rewrite (BK 20%bv ltac:(wkeep_in)). exact R20.
  - rewrite (BK 21%bv ltac:(wkeep_in)). exact R21.
  - rewrite (BK 27%bv ltac:(wkeep_in)). exact R27.
  - rewrite (wpres_bv _ _ HPB 24%bv ltac:(wcs)). exact A24.
  - apply (wun_val _ _ _ _ _ _ _ UB AL); [lia | lia | intros x Hx; unfold ESTACK; lia].
  - exact NBsh.
  - exact NBpp.
  - exact Hpp16.
  - exact Happ.
  - exact Hpphi.
  - lia.
  - exact HL8.
  - lia. }
intros W' c' _ (-> & regsB2 & memB2 & mdB2 & -> & HJB2 & HioB2 & B21 & B210 & B211 & B212 & B224 & B2K & B2L & B2U).
assert (UB2 : wun (w_H W2) memB memB2 (fun a => pp + 0x4000 <= a < pp + 0x4000 + 8))
  by (intros a Ha Hn; apply B2U; [exact Ha | exact Hn]).
destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJB2 Hpp2 Hfin HFa) as (NB2sh & NB2pp & NB2F & NB2Fs & NB2ra & NB2hl).
assert (B2K' : forall r : bv 5, In r wkeep -> getr regsB2 r = getr regs2 r) by (intros r0 Hr0; rewrite (B2K r0 Hr0); exact (BK r0 Hr0)).
(* ------------------------------ M2: __asan_memset(pp + L + 8 + size, 0, pad) ------------------------------ *)
set (pad := Model.pad8 sz) in *.
assert (BR2 : getr regsB2 2 = w64 R) by (rewrite (B2K' 2%bv ltac:(wkeep_in)); exact R2).
assert (BR3 : getr regsB2 3 = w64 (as_gp B)) by (rewrite (B2K' 3%bv ltac:(wkeep_in)); exact R3).
assert (BR4 : getr regsB2 4 = w64 (as_tp B)) by (rewrite (B2K' 4%bv ltac:(wkeep_in)); exact R4).
assert (HspB2 : spZ regsB2 = sp0 + (R - sp0)) by (unfold spZ; rewrite BR2, Hspo; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ apply (w_intrin_at B OSet 0x51570 AMEMSET W2 regsB2 memB2 STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
    (x_md0 cx) (x_own cx) ly2 S2 mdB2 (x_k cx) (pp + L + 8 + sz) 0 pad (R - sp0) (getr regsB2 1) HJB2 B210 B211 B212).
  - lia.
  - lia.
  - lia.
  - exact HspB2.
  - exact Ho16.
  - lia.
  - unfold ESTACK; lia.
  - exact BR3.
  - exact BR4.
  - reflexivity.
  - rewrite B21. exact w_ret_C.
  - intros a Ha. split; [apply Hawpp; lia | unfold ESTACK; lia].
  - apply HappL; lia.
  - apply (NB2ra (pp + L + 8 + sz) pad); lia.
  - intros Hn. apply (NB2ra (pp + L + 8 + sz) pad); lia.
  - exact I. }
intros W' c' _ (-> & regsM & memM & mdM & -> & HJM & HioM & HPM & M10 & Mset & MU & Mpres).
rewrite B21.
assert (UM : wun (w_H W2) memB2 memM (fun a => pp + L + 8 + sz <= a < pp + L + 8 + sz + pad \/ R - ESTACK <= a < R)).
{ intros a Ha Hn. apply MU; [exact Ha | intros Hx; apply Hn; left; lia | intros Hx; apply Hn; right; lia]. }
destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJM Hpp2 Hfin HFa) as (NMsh & NMpp & NMF & NMFs & NMra & NMhl).
assert (MK : forall r : bv 5, In r wkeep -> getr regsM r = getr regs2 r).
{ intros r0 Hr0. rewrite (wkeep_saved _ _ HPM r0 Hr0). exact (B2K' r0 Hr0). }
assert (M24 : getr regsM 24 = w64 pad) by (rewrite (wpres_bv _ _ HPM 24%bv ltac:(wcs)); exact B224).
(* what the four steps so far changed: the pod's bytes, len and the callees' stack *)
set (P1 := fun a => pp + L <= a < pp + L + 8 + sz + pad \/ pp + 0x4000 <= a < pp + 0x4000 + 8 \/ R - ESTACK <= a < R).
assert (U2M : wun (w_H W2) mem2 memM P1).
{ apply (wun_mono _ _ _ _ _ (wun_trans _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UA UB) UB2) UM)).
  intros a Ha HP0. unfold P1. lia. }
assert (HSLM : Forall (fun c => val_mem rsegs (mrestrict (w_H W2) memM) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp fs kk cnt)).
{ apply (wun_slots _ _ _ _ R _ U2M HSL). intros c Hc. unfold wslot_vals in Hc. cbn [In] in Hc.
  repeat destruct Hc as [<- | Hc]; try contradiction; cbn [fst]; unfold P1, ESTACK;
  (split; [lia | split; [lia | intros x Hx; lia]]). }
assert (HLM : val_mem rsegs (mrestrict (w_H W2) memM) (pp + 0x4000) 8 (L + 8 + sz)).
{ apply (wun_val _ _ _ _ _ _ _ UM B2L); [lia | lia | intros x Hx; unfold ESTACK; lia]. }
assert (HFSHM : rl_fsh rsegs (w_H W2) memM F rs_PJ).
{ apply (wun_fsh _ _ _ _ F rs_PJ U2M HFSH); [lia | change (Z.of_nat (length rs_PJ)) with 52; lia |].
  change (Z.of_nat (length rs_PJ)) with 52. intros j Hj. unfold P1, ESTACK. destruct HsppF; lia. }
assert (HEMM : rm_bytes rsegs (w_H W2) memM (F + 0xf0) (ent_mem ed)).
{ apply (wun_bytes _ _ _ _ _ _ U2M HEM); rewrite ?Hlem; try lia; intros x Hx; unfold P1, ESTACK; destruct HpF; lia. }
set (last := (Z.of_nat (S k) =? cnt)).
assert (Hkk1 : Z.of_nat (S k) = kk + 1) by (unfold kk; rewrite Hk, Nat2Z.inj_succ; ring).
assert (Hlast : (kk + 1 =? cnt) = last) by (unfold last; rewrite Hkk1; reflexivity).
assert (Hexit : w64 (w_exitF last) = Z_to_bv 64 (w_exit last)) by (destruct last; reflexivity).
assert (Hio2M : same_io md2 mdM).
{ apply (same_io_trans _ _ _ HioA). apply (same_io_trans _ _ _ HioB). apply (same_io_trans _ _ _ HioB2). exact HioM. }
(* the pod's bytes pod_write_ent left at buf[L] (pod.h:200-206): size, type, body, pad *)
assert (UAM : wun (w_H W2) memA memM (fun a => pp + L + 8 <= a < pp + L + 8 + sz + pad \/ pp + 0x4000 <= a < pp + 0x4000 + 8 \/ R - ESTACK <= a < R)).
{ apply (wun_mono _ _ _ _ _ (wun_trans _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UB UB2) UM)). intros a Ha HP0. lia. }
assert (Hbody' : Z.of_nat (length (e_body ed)) = sz) by (rewrite Hbody; unfold sz; lia).
assert (HENCM : rm_bytes rsegs (w_H W2) memM (pp + L) (enc_pod ed)).
{ unfold enc_pod. apply w_enc_bytes.
  - apply (wun_bytes _ _ _ _ _ _ UAM (rm_bytes_of_val rsegs _ _ _ _ _ Asz)); rewrite ?length_Z_to_le_bytes; try lia.
    intros x Hx. unfold ESTACK. lia.
  - apply (wun_bytes _ _ _ _ _ _ UAM (rm_bytes_of_val rsegs _ _ _ _ _ Aty)); rewrite ?length_Z_to_le_bytes; try lia.
    intros x Hx. unfold ESTACK. lia.
  - assert (HCB : rm_bytes rsegs (w_H W2) memB (pp + L + 8) (e_body ed)).
    { apply (rm_memcpy_bytes rsegs (w_H W2) memA (w_H W2) memB (F + 0xf8) (pp + L + 8) (e_body ed) (w_body_of _ _ _ _ HEMA)).
      intros i0 Hi0. rewrite Hbody' in Hi0. exact (Bcpy i0 Hi0). }
    apply (wun_bytes _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UB2 UM) HCB); rewrite ?Hbody'; try lia.
    intros x Hx. unfold ESTACK. lia.
  - rewrite Hbody'.
    apply (rm_memset_bytes rsegs (w_H W2) memM (pp + L + 8 + sz) 0 (Z.to_nat pad)).
    intros i0 Hi0. rewrite Z2Nat.id in Hi0 by lia. exact (Mset i0 Hi0). }
assert (Henc : Z.of_nat (length (enc_pod ed)) = 8 + sz + pad) by exact (Model.zlen_enc_pod ed Hwf).
destruct Hfs01 as [Hf0 | Hf1].
- (* ---------------- the pod's struct was opened before (first = 0): C -> the loop's exit ---------------- *)
  assert (HfstF : pc_first (PbCut sh ps (Some es)) = false)
    by (rewrite Hfs in Hf0; destruct (pc_first (PbCut sh ps (Some es))); [discriminate | reflexivity]).
  rewrite Hf0 in HSLM.
  eapply SRr_bind.
  { apply (w_blkC0 B STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 regsM memM mdM
      (x_k cx) R F pp L sz kk cnt sF last HJM Hpp2 Hfr (w_fsh_awr STK sp0 (x_FP cx) _ _ ly2 (x_own cx) (x_pos cx) F Hown HFa)).
    - rewrite (MK 9%bv ltac:(wkeep_in)). exact R9.
    - rewrite (MK 19%bv ltac:(wkeep_in)). exact R19.
    - rewrite (MK 20%bv ltac:(wkeep_in)). exact R20.
    - rewrite (MK 21%bv ltac:(wkeep_in)). exact R21.
    - rewrite (MK 23%bv ltac:(wkeep_in)). exact R23.
    - rewrite (MK 27%bv ltac:(wkeep_in)). exact R27.
    - exact M24.
    - exact HSLM.
    - exact HLM.
    - exact NMsh.
    - exact NMpp.
    - intros o Ho. apply NMFs. lia.
    - exact Hpp16.
    - exact Happ.
    - exact Hpphi.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HshFpp.
    - lia.
    - exact HL8.
    - lia.
    - lia.
    - lia.
    - exact Hlast. }
  intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & C11 & CK & CL & Cfsh & CU).
  assert (UC : wun (w_H W2) memM mem3 (fun a => pp + 0x4000 <= a < pp + 0x4000 + 8 \/ sF + 30 <= a < sF + 43))
    by (intros a Ha Hn; apply CU; [exact Ha | tauto | tauto]).
  rewrite <- Hexit.
  apply (w_finish B MT cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed regs3 mem3 md3 last HP Hi Hk HJcut
    HFC HFCL eq_refl HJ3).
  + exact (same_io_trans _ _ _ Hio2M Hio3).
  + intros r0 Hr0. rewrite (CK r0 Hr0). exact (MK r0 Hr0).
  + rewrite C11, Hkk1. reflexivity.
  + intros a Ha H1 H2 H3. change (e_R (x_e cx)) with R in H1. change (e_pp (x_e cx)) with pp in H2.
    change (shadow_addr (e_F (x_e cx))) with sF in H3. unfold Layout.PP_SIZE in H2.
    rewrite (UC a Ha) by lia. apply U2M; [exact Ha | unfold P1; lia].
  + intros o Ho. fold F sF. exact (Cfsh o Ho).
  + apply (wi_loc (w_H W2) mem2 mem3 pp sh ps es ed L sz pad kk HPV HPE HES Hwf Hps2 Hes32 ltac:(lia) ltac:(lia)
      eq_refl eq_refl eq_refl eq_refl HIMG).
    * apply (wun_bytes _ _ _ _ _ _ UC HENCM); rewrite ?Henc; try lia; intros x Hx; destruct HsppF; lia.
    * exact CL.
    * intros Hft. rewrite HfstF in Hft. discriminate.
    * intros a Ha H1 H2 _. rewrite (UC a ltac:(lia)) by (destruct HsppF; lia). apply U2M; [lia | unfold P1, ESTACK; lia].
- (* ---------------- the params Struct's first pod (first = 1): C -> the record's memcpy -> D -> exit ---------------- *)
  assert (HfstT : pc_first (PbCut sh ps (Some es)) = true)
    by (rewrite Hfs in Hf1; destruct (pc_first (PbCut sh ps (Some es))); [reflexivity | discriminate]).
  rewrite Hf1 in HSLM.
  assert (HNEM : val_mem rsegs (mrestrict (w_H W2) memM) (pp + 0x4d14) 4 kk).
  { apply (wun_val _ _ _ _ _ _ _ U2M (HNE Hf1)); [lia | lia | intros x Hx; unfold P1, ESTACK; lia]. }
  eapply SRr_bind.
  { apply (w_blkC1 B STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 regsM memM mdM
      (x_k cx) R F pp L sz kk cnt kk HJM Hpp2 Hfr).
    - rewrite (MK 9%bv ltac:(wkeep_in)). exact R9.
    - rewrite (MK 20%bv ltac:(wkeep_in)). exact R20.
    - rewrite (MK 21%bv ltac:(wkeep_in)). exact R21.
    - rewrite (MK 23%bv ltac:(wkeep_in)). exact R23.
    - rewrite (MK 27%bv ltac:(wkeep_in)). exact R27.
    - exact M24.
    - exact HSLM.
    - exact HLM.
    - exact HNEM.
    - exact NMsh.
    - exact NMpp.
    - exact Hpp16.
    - exact Happ.
    - exact Hpphi.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact HL8.
    - lia.
    - lia.
    - lia.
    - lia. }
  intros W' c' _ (-> & regsC & memC & mdC & -> & HJC & HioC & C1 & C10 & C11 & C12 & CK & CL & CN & CU).
  assert (UC : wun (w_H W2) memM memC (fun a => pp + 0x4000 <= a < pp + 0x4000 + 8 \/ pp + 0x4d14 <= a < pp + 0x4d14 + 4))
    by (intros a Ha Hn; apply CU; [exact Ha | tauto | tauto]).
  destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJC Hpp2 Hfin HFa) as (NCsh & NCpp & NCF & NCFs & NCra & NChl).
  assert (CK' : forall r : bv 5, In r wkeep -> getr regsC r = getr regs2 r) by (intros r0 Hr0; rewrite (CK r0 Hr0); exact (MK r0 Hr0)).
  assert (CR2 : getr regsC 2 = w64 R) by (rewrite (CK' 2%bv ltac:(wkeep_in)); exact R2).
  assert (CR3 : getr regsC 3 = w64 (as_gp B)) by (rewrite (CK' 3%bv ltac:(wkeep_in)); exact R3).
  assert (CR4 : getr regsC 4 = w64 (as_tp B)) by (rewrite (CK' 4%bv ltac:(wkeep_in)); exact R4).
  assert (HspC : spZ regsC = sp0 + (R - sp0)) by (unfold spZ; rewrite CR2, Hspo; apply unsigned_lit_small; lia).
  assert (HFSHC : rl_fsh rsegs (w_H W2) memC F rs_PJ).
  { apply (wun_fsh _ _ _ _ F rs_PJ UC HFSHM); [lia | change (Z.of_nat (length rs_PJ)) with 52; lia |].
    change (Z.of_nat (length rs_PJ)) with 52. intros j Hj. destruct HsppF; lia. }
  assert (HFSHCe := HFSHC). rewrite rs_PJ_e in HFSHCe.
  assert (HEMC : rm_bytes rsegs (w_H W2) memC (F + 0xf0) (ent_mem ed)).
  { apply (wun_bytes _ _ _ _ _ _ UC HEMM); rewrite ?Hlem; try lia; intros x Hx; destruct HpF; lia. }
  (* ---------------- M3: __asan_memcpy(&ent[n_ent], &e, 104) ---------------- *)
  eapply SRr_bind.
  { apply (w_intrin_at B OCpy 0x510d4 AMEMCPY W2 regsC memC STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx)
      (x_md0 cx) (x_own cx) ly2 S2 mdC (x_k cx) (pp + 0x4014 + 104 * kk) (F + 0xf0) 104 (R - sp0) (getr regsC 1) HJC C10 C11 C12).
    - lia.
    - lia.
    - lia.
    - exact HspC.
    - exact Ho16.
    - lia.
    - unfold ESTACK; lia.
    - exact CR3.
    - exact CR4.
    - reflexivity.
    - rewrite C1. exact w_ret_D.
    - intros a Ha. split; [apply Hawpp; lia | unfold ESTACK; lia].
    - apply HappL; lia.
    - apply (NCra (pp + 0x4014 + 104 * kk) 104); lia.
    - intros Hn. apply (NCra (pp + 0x4014 + 104 * kk) 104); lia.
    - cbn iota. split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply (aview_some_of_apresent rsegs); replace a with (F + (a - F)) by lia; apply NCF; lia
        | rewrite HspC; unfold ESTACK; lia]. }
      split; [destruct HpF; [left | right]; lia|]. split; [apply HappF; lia|]. split.
      { pose proof (rm_A_ra_e rsegs _ _ F false false false false 0 104 HFSHCe HF8 ltac:(lia) ltac:(lia)) as Hra.
        unfold RM_E in Hra. replace (F + 0xf0) with (F + 0xf0 + 0) by lia. exact Hra. }
      intros Hn. apply NChl; lia. }
  intros W' c' _ (-> & regsD & memD & mdD & -> & HJD & HioD & HPD & D10 & Dcpy & DU & Dpres).
  rewrite C1.
  assert (UD : wun (w_H W2) memC memD (fun a => pp + 0x4014 + 104 * kk <= a < pp + 0x4014 + 104 * kk + 104 \/ R - ESTACK <= a < R)).
  { intros a Ha Hn. apply DU; [exact Ha | intros Hx; apply Hn; left; lia | intros Hx; apply Hn; right; lia]. }
  destruct (w8_now B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pp F (x_pos cx) HJD Hpp2 Hfin HFa) as (NDsh & NDpp & NDF & NDFs & NDra & NDhl).
  assert (DK : forall r : bv 5, In r wkeep -> getr regsD r = getr regs2 r).
  { intros r0 Hr0. rewrite (wkeep_saved _ _ HPD r0 Hr0). exact (CK' r0 Hr0). }
  assert (HSLD : Forall (fun c => val_mem rsegs (mrestrict (w_H W2) memD) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp 1 kk cnt)).
  { apply (wun_slots _ _ _ _ R _ (wun_trans _ _ _ _ _ _ UC UD) HSLM). intros c Hc. unfold wslot_vals in Hc. cbn [In] in Hc.
    repeat destruct Hc as [<- | Hc]; try contradiction; cbn [fst]; unfold ESTACK;
    (split; [lia | split; [lia | intros x Hx; lia]]). }
  (* ---------------- D: 0x81850 -> the loop's exit ---------------- *)
  eapply SRr_bind.
  { apply (w_blkD B STK sp0 (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) ly2 S2 W2 regsD memD mdD
      (x_k cx) R F pp kk cnt sF last HJD (w_fsh_awr STK sp0 (x_FP cx) _ _ ly2 (x_own cx) (x_pos cx) F Hown HFa)).
    - rewrite (DK 9%bv ltac:(wkeep_in)). exact R9.
    - rewrite (DK 19%bv ltac:(wkeep_in)). exact R19.
    - rewrite (DK 27%bv ltac:(wkeep_in)). exact R27.
    - exact HSLD.
    - intros o Ho. apply NDFs. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hlast. }
  intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & Hio3 & E11 & EK & Efsh & EU).
  assert (UE : wun (w_H W2) memD mem3 (fun a => sF + 30 <= a < sF + 43)) by (intros a Ha Hn; apply EU; [exact Ha | exact Hn]).
  rewrite <- Hexit.
  apply (w_finish B MT cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed regs3 mem3 md3 last HP Hi Hk HJcut
    HFC HFCL eq_refl HJ3).
  + apply (same_io_trans _ _ _ Hio2M). apply (same_io_trans _ _ _ HioC). apply (same_io_trans _ _ _ HioD). exact Hio3.
  + intros r0 Hr0. rewrite (EK r0 Hr0). exact (DK r0 Hr0).
  + rewrite E11, Hkk1. reflexivity.
  + intros a Ha H1 H2 H3. change (e_R (x_e cx)) with R in H1. change (e_pp (x_e cx)) with pp in H2.
    change (shadow_addr (e_F (x_e cx))) with sF in H3. unfold Layout.PP_SIZE in H2.
    rewrite (UE a Ha) by lia. rewrite (UD a Ha) by (unfold ESTACK in *; lia). rewrite (UC a Ha) by lia.
    apply U2M; [exact Ha | unfold P1; lia].
  + intros o Ho. fold F sF. exact (Efsh o Ho).
  + apply (wi_loc (w_H W2) mem2 mem3 pp sh ps es ed L sz pad kk HPV HPE HES Hwf Hps2 Hes32 ltac:(lia) ltac:(lia)
      eq_refl eq_refl eq_refl eq_refl HIMG).
    * apply (wun_bytes _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UC UD) UE) HENCM);
        rewrite ?Henc; try lia; intros x Hx; unfold ESTACK; destruct HsppF; lia.
    * apply (wun_val _ _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UD UE) CL); [lia | lia | intros x Hx; unfold ESTACK; destruct HsppF; lia].
    * intros _. split.
      -- apply (wun_val _ _ _ _ _ _ _ (wun_trans _ _ _ _ _ _ UD UE) CN); [lia | lia | intros x Hx; unfold ESTACK; destruct HsppF; lia].
      -- assert (HRD : rm_bytes rsegs (w_H W2) memD (pp + 0x4014 + 104 * kk) (ent_mem ed)).
         { apply (rm_memcpy_bytes rsegs (w_H W2) memC (w_H W2) memD (F + 0xf0) _ (ent_mem ed) HEMC).
           intros i0 Hi0. rewrite Hlem in Hi0. exact (Dcpy i0 Hi0). }
         apply (wun_bytes _ _ _ _ _ _ UE HRD); rewrite ?Hlem; try lia; intros x Hx; destruct HsppF; lia.
    * intros a Ha H1 H2 H3. destruct (H3 HfstT) as [H4 H5].
      rewrite (UE a ltac:(lia)) by (destruct HsppF; lia). rewrite (UD a ltac:(lia)) by (unfold ESTACK; lia).
      rewrite (UC a ltac:(lia)) by lia. apply U2M; [lia | unfold P1, ESTACK; lia].
Qed.
End w.
