(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): part 3 of segment E01 of the walk of LLVMFuzzerTestOneInput, the body
   0x80dfc -> the malloc entry 0x53060 (lib/A/HPgE01D.v e01_body_stmt). Proves no function
   (kind: segment lemma of LLVMFuzzerTestOneInput's walk, part 3 of 4).

   THE CODE (lib/A/HPgE01D.v E01_TBL, read from image A's loaded segments):
     0x80dfc  `beqz s2` (s2 = n): n = 0 -> 0x80e3c `sd zero,64(s1)`, s5 = s8 = 0, `j 0x80e84`;
     0x80e00 .. 0x80e10  the check of data[0]: `srli a0,s11,3; add a0,a0,s7; lb a0,0(a0); beqz a0,+8;
                         j 0x83888`, and the slow block 0x83888 `andi a1,s11,7; bge a1,a0` to the report
                         0x83894, `j 0x80e14`;
     0x80e14 .. 0x80e24  `lbu a1,0(s11)`; a0 = s11 + 1; a2 = 1; a1 = data[0] & 1; `sd a1,64(s1)`;
     0x80e28  `bne s2,a2`: n = 1 -> s5 = s8 = 0, s11 = p + 1, `j 0x80e84`;
     0x80e4c .. 0x80e5c  the check of data[1] at p + 1, slow block 0x83900 `andi a2,a0,7; bge a2,a1` to
                         0x8390c, `j 0x80e60`;
     0x80e60 .. 0x80e80  `lbu a0,0(a0)`; s5 = n - 2; s11 = p + 2; s8 = data[1] - 10 ((205 data[1]) >> 11);
     0x80e84 .. 0x80e90  s4 = 0x5000; s2 = a0 = 19744; `jal` 0x53060 with ra = 0x80e94.
   The two reports 0x83894 and 0x8390c are in no run: the input block's shadow byte is 0 when at least eight
   bytes are left and n (1 .. 7) otherwise, and the cursor is 16-aligned (the blocks law), so at both checks
   the slow block's `bge` compares 0 (p & 7) or 1 ((p + 1) & 7) with that byte and is not taken.

   THE FOUR RUNS. The walk is split on the input's length, which fixes both branches and the shadow byte the
   two checks read, so every run of the engine is straight-line:
     n = 0        the `beqz` is taken (0x80dfc -> 0x80e3c -> 0x80e84);
     n = 1        the shadow byte is 1 (the block's last, partial granule), the `bne` is taken;
     2 <= n <= 7  the shadow byte is n, both checks take their slow block;
     n >= 8       the shadow byte is 0, both checks pass at once.
   The only region the runs write is the null-flag slot R+0x40; the input's shadow byte (atom 32, reached by
   the alias the checks' `srli; add` forms) and its first one or two bytes (atom 27, the cursor) are one-byte
   read-only regions. lib/A/HPgE01B0.v holds the helpers. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls HPgMem HPgSteps HPgE01D HPgE01B0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ============================ the symbolic values the two checks need ============================ *)
(* the shadow address the check forms: (cursor >> 3) + K, aliased to the shadow cell's atom 32 *)
Definition E01B_ASH0 : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 0) (SLit 3)) (SOff 23 0), SOff 32 0).
Definition E01B_ASH1 : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 1) (SLit 3)) (SOff 23 0), SOff 32 0).
(* the slow blocks' `andi u,x,7` at a 16-aligned cursor *)
Definition E01B_AND0 : sv * sv := (SAlu ALU_AND (SOff 27 0) (SLit 7), SLit 0).
Definition E01B_AND1 : sv * sv := (SAlu ALU_AND (SOff 27 1) (SLit 7), SLit 1).
Definition e01b_cs1 : list YP09.chunk := [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition e01b_cs2 : list YP09.chunk := [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))].

Section d.
Lemma e01b_den : forall E X v, U E X = v -> sv_denot E X = w64 v.
Proof. intros E X v <-. unfold U, w64. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma e01b_at : forall E k v, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff k 0) = w64 v.
Proof. intros E k v Hk Hv. apply e01b_den. apply U_atom; [exact Hk | exact Hv]. Qed.
Lemma e01b_off : forall E k c v u, ew E k = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> v + c = u ->
sv_denot E (SOff k c) = w64 u.
Proof. intros E k c v u Hk Hv Hc <-. apply e01b_den. apply U_atom_off; assumption. Qed.
(* `andi a1,a1,1` 0x80e20: the null flag *)
Lemma e01b_null : forall E k v, ew E k = w64 v -> 0 <= v < 256 ->
sv_denot E (SAlu ALU_AND (SOff k 0) (SLit 1)) = w64 (Z.land v 1).
Proof.
intros E k v Hk Hv.
assert (Hu : U E (SOff k 0) = v) by (apply U_atom; [exact Hk | lia]).
assert (HL : 0 <= Z.land v 1 <= 1) by (apply Z_land_upper; lia).
apply e01b_den. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hu, U_SLit.
change (zcanon 1) with 1. apply zcanon_id. unfold M64. lia.
Qed.
(* 0x80e6c .. 0x80e80: the cap byte mod 10 *)
Lemma e01b_cap : forall E k v, ew E k = w64 v -> 0 <= v < 256 ->
sv_denot E (SAlu ALU_SUB (SOff k 0)
  (SMd M_MUL (SAlu ALU_SRL (SMd M_MUL (SOff k 0) (SLit 205)) (SLit 11)) (SLit 10))) = w64 (v mod 10).
Proof.
intros E k v Hk Hv.
assert (Hu : U E (SOff k 0) = v) by (apply U_atom; [exact Hk | lia]).
assert (Hq : 0 <= 205 * v / 2048 < 26).
{ split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof (Z.mod_pos_bound v 10 ltac:(lia)) as Hm.
assert (HM : v - 10 * (205 * v / 2048) = v mod 10) by (apply e01b_mod10; lia).
apply e01b_den.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hu.
rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite U_SMd. cbn [zmd_raw]. rewrite Hu, U_SLit.
change (zcanon 205) with 205. change (zcanon 11) with 11. change (zcanon 10) with 10.
rewrite (zcanon_id (v * 205)) by (unfold M64; lia).
change (Z.land 11 63) with 11. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 11) with 2048.
rewrite (Z.mul_comm v 205).
rewrite (zcanon_id (205 * v / 2048)) by (unfold M64; lia).
rewrite (zcanon_id (205 * v / 2048 * 10)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the alias of the second check's shadow address: (p + 1) >> 3 = p >> 3 when p is 8-aligned *)
Lemma e01b_ash1 : forall E (kp kb ks : nat) pv Bv,
ew E kp = w64 pv -> 0 <= pv -> pv + 1 < 2 ^ 64 -> pv mod 8 = 0 ->
ew E kb = w64 Bv -> 0 <= Bv -> Bv + pv / 8 < 2 ^ 64 -> ew E ks = w64 (Bv + pv / 8) ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff kp 1) (SLit 3)) (SOff kb 0)) = sv_denot E (SOff ks 0).
Proof.
intros E kp kb ks pv Bv Hp H0 H1 H8 Hb Hb0 Hb1 Hs.
assert (Hd : 0 <= pv / 8) by (apply Z.div_pos; lia).
assert (Hup : U E (SOff kp 1) = pv + 1) by (apply U_atom_off; [exact Hp | lia | lia]).
assert (Hub : U E (SOff kb 0) = Bv) by (apply U_atom; [exact Hb | lia]).
assert (Hus : U E (SOff ks 0) = Bv + pv / 8) by (apply U_atom; [exact Hs | lia]).
assert (Hdd : (pv + 1) / 8 = pv / 8).
{ pose proof (Z.div_mod pv 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
  rewrite D at 1. replace (8 * (pv / 8) + 1) with (1 + (pv / 8) * 8) by lia.
  rewrite Z_div_plus_full by lia. rewrite (Z.div_small 1 8) by lia. lia. }
apply U_inj. rewrite Hus, U_SAlu. cbn [zalu_raw]. rewrite Hub, U_SAlu. cbn [zalu_raw].
rewrite Hup, U_SLit. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Hdd, (zcanon_id (pv / 8)) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* the slow blocks' `andi u,x,7` at a 16-aligned cursor plus c *)
Lemma e01b_and7 : forall E (k : nat) pv c, ew E k = w64 pv -> 0 <= pv -> pv + c < 2 ^ 64 -> pv mod 8 = 0 ->
0 <= c < 8 -> sv_denot E (SAlu ALU_AND (SOff k c) (SLit 7)) = sv_denot E (SLit c).
Proof.
intros E k pv c Hk H0 H1 H8 Hc.
assert (Hu : U E (SOff k c) = pv + c) by (apply U_atom_off; [exact Hk | lia | lia]).
assert (HA : Z.land (pv + c) 7 = (pv + c) mod 8).
{ change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. }
pose proof (Z.div_mod pv 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
assert (HB : (pv + c) mod 8 = c).
{ replace (pv + c) with (c + (pv / 8) * 8) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
apply U_inj. rewrite U_SLit, U_SAlu. cbn [zalu_raw]. rewrite Hu, U_SLit.
change (zcanon 7) with 7. rewrite HA, HB.
reflexivity.
Qed.
End d.

(* a register the run kept: its symbolic value is still its own entry atom (gp and tp, whose values the
   symbol record fixes without a range) *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma e01b_keepreg : forall H E ss ms regs0 extra (r : bv 5) k,
st_ok rsegs E ss (restrict H ms) -> E = Ereg regs0 extra -> sr_get (ss_regs ss) r = SOff k 0 -> (k < 32)%nat ->
getr (ms_regs ms) r = getr regs0 (Z_to_bv 5 (Z.of_nat k)).
Proof.
intros H E ss ms regs0 extra r k HS HE Hsr Hk.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hsr. apply bv_eq. rewrite denot_SOff, Z.add_0_r, HE.
rewrite (ew_Ereg_nat regs0 extra k (Z_to_bv 5 (Z.of_nat k))).
- apply zcanon_id. pose proof (bv_unsigned_in_range 64 (getr regs0 (Z_to_bv 5 (Z.of_nat k)))) as Hb.
  change (bv_modulus 64) with (2 ^ 64) in Hb. unfold M64. lia.
- rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 5) with 32. lia.
Qed.
End r.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the real frame [R, S) fits under the harness's stack budget *)
Hypothesis HSTK : 0x1f0 + ASTACK <= LLVMF_STK.
(* the empty input's address, which the harness's caller passes when n = 0 *)
Hypothesis HAE : 0 < A_EMPTY < kLowMemEnd.

Theorem e01_body_ok : e01_body_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx pos e ly1 S1 W1 regs1 mem1 md1 HB HH.
unfold hq_base in HB.
destruct HB as (HPRE & Hra & Hp10 & Hn11 & Hpn & Hnl & Hpl & Hfr0 & Hev & Hlive & HROD).
destruct HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold e01_hdr_facts in HH.
destruct HH as (HJ1 & Eab & HGeo & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R26 & R27 & HFSH & HKEPT).
destruct HGeo as (ES & ER & EF).
remember (h_p rsegs hx) as p eqn:Ep. remember (h_n rsegs hx) as n eqn:En.
remember (h_pl rsegs hx) as pl eqn:Epl.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as [Hcl _].
assert (HASTK : ASTACK = 16384) by reflexivity.
(* ---- the geometry: S, R and the frame F ---- *)
destruct (e01b_geo (e_S e) (e_R e) ER) as [HRlo HRhi].
assert (HSb : alloc_ceiling + LLVMF_STK <= e_S e <= 2 ^ 47) by (rewrite ES; lia).
assert (HRb : alloc_ceiling <= e_R e /\ e_R e + 0x48 <= e_S e - 0x198) by (rewrite HASTK in HSTK; lia).
unfold hq_j in HJ1.
pose proof HJ1 as (HAR1 & Hle & _ & _ & _ & Hfrs & _ & _ & Kout1 & Kblk1 & _ & _ & _ & Hpres1 & _ & _ & _).
assert (Hfin : In (HQ_CID, pos) (frames S1)) by (rewrite Hfrs, Hfr0; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly1 HAR0 Hle) as (_ & Hfa & _).
assert (EF1 : e_F e = frame_addr ly1 HQ_CID pos) by (rewrite EF, Hfa; reflexivity).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ HQ_CID pos HAR1 Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ HQ_CID pos HAR1 Hfin) as (HF32 & _ & _ & _).
change (fs_frame_bytes HQ_CID) with 1024 in HFceil, HFapp.
rewrite <- EF1 in HF4096, HFceil, HFapp, HF32.
assert (HFd : 0 <= e_F e / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hshf : 0 <= shadow_addr (e_F e) /\ shadow_addr (e_F e) + 80 <= alloc_ceiling)
  by (unfold shadow_addr, SHADOW_OFF; lia).
(* ---- the slot R+0x40 is present, and what the runs keep ---- *)
assert (HP40 : forall o, 0x40 <= o < 0x48 -> apresent (w_H W1) mem1 (e_R e + o)).
{ intros o Ho. apply Hpres1. rewrite <- ES. rewrite HASTK in HSTK. lia. }
assert (Hn0 : 0 <= n) by lia.
assert (HRr : 0 <= e_R e < 2 ^ 64) by (revert HRb HSb Hcl; clear; intros; lia).
assert (HSr : 0 <= e_S e < 2 ^ 64) by (revert HRb HSb Hcl; clear; intros; lia).
assert (HFrng : 0 <= e_F e < 2 ^ 64) by (revert HF4096 HFceil Hcl; clear; intros; lia).
assert (HShr : 0 <= shadow_addr (e_F e) < 2 ^ 64) by (revert Hshf Hcl; clear; intros; lia).
assert (HSHr : 0 <= SHADOW_OFF < 2 ^ 64) by (unfold SHADOW_OFF; clear; lia).
assert (HKS : e_R e + 0x48 <= e_S e - 0x80) by (revert HRb; clear; intros; lia).
assert (HKF : e_F e + HQ_FLAG + 8 <= e_R e + 0x40)
  by (unfold HQ_FLAG; revert HFceil HRb; clear; intros; lia).
assert (HKSH : shadow_addr (e_F e) + 80 <= e_R e + 0x40) by (revert Hshf HRb; clear; intros; lia).
assert (HS80 : 0 <= e_S e - 0x80) by (revert HRb Hcl; clear; intros; lia).
assert (HFf : e_F e + HQ_FLAG + 8 <= 2 ^ 64) by (unfold HQ_FLAG; revert HFceil Hcl; clear; intros; lia).
assert (HR0 : 0 <= e_R e) by (revert HRb Hcl; clear; intros; lia).
assert (HR48 : e_R e + 0x48 <= 2 ^ 64) by (revert HKS HSr; clear; intros; lia).
assert (HRac : alloc_ceiling <= e_R e + 0x40) by (revert HRb; clear; intros; lia).
(* ---- the four runs ---- *)
assert (Hcase : n = 0 \/ n = 1 \/ (2 <= n <= 7) \/ 8 <= n) by lia.
destruct Hcase as [Hc | [Hc | [Hc | Hc]]].
- (* ================= n = 0: the `beqz` is taken ================= *)
  assert (Hpe : p = A_EMPTY) by (destruct Hpn as [[_ H] | [H _]]; [exact H | lia]).
  assert (Hpl0 : h_pl rsegs hx = []) by (rewrite <- Epl; destruct pl as [|b l]; [reflexivity | cbn [length] in Hnl; lia]).
  pose proof (e01b_entry0 W1 regs1 mem1 (e_R e) sr_atoms (regs_ok_Ereg regs1 []) R9
    ltac:(lia) ltac:(lia) HP40) as HS0.
  assert (R18' : getr (ms_regs (restrict (w_H W1) (mkst regs1 (w64 E01_HDR) mem1 (seg_rom rsegs)))) 18%bv
    = Z_to_bv 64 0) by (cbn [ms_regs restrict mkst]; rewrite R18, Hc; reflexivity).
  pose proof (st_ok_pin_lit rsegs _ _ _ 18%bv 0 HS0 ltac:(vm_compute; reflexivity) R18') as HS.
  clear HS0 R18'. cbn [ss_pc ss_mem ss_resv ss_facts ss_regs] in HS.
  unfold cfg_at.
  aj_run_to E01_TBL_ok HS HJ1 E01_MALLOC.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (e_R e - e_S e));
    [ reflexivity
    | rewrite (ew_Ereg_nat regs1 [] 9 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia;
      rewrite ES; lia
    | cbn; rewrite HASTK in HSTK; lia | cbn; lia |].
    apply awr_ok_nil. }
  (* the run writes only the null-flag slot *)
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (e_R e + 0x40 <= x < e_R e + 0x48) ->
    aview rsegs (w_H W1) (ms_mem ms) x = aview rsegs (w_H W1) mem1 x).
  { apply (e01b_keep _ _ _ _ _ _ HFr).
    intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    rewrite (ew_Ereg_nat regs1 [] 9 9%bv eq_refl), R9 in Ha. unfold w64 in Ha.
    rewrite unsigned_lit_small in Ha by lia. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl). cbn [ss_pc].
  apply SRr_ret.
  exists pos, (e01b_env (e_S e) (e_R e) (e_F e) A_EMPTY 0 0 0 []), ([] : list byte), ly1, S1,
         (ms_regs ms), (ms_mem ms).
  eexists. split; [reflexivity|].
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RG.
  assert (U9 : bv_unsigned (ew (Ereg regs1 ([] : list word)) 9) = e_R e)
    by (rewrite (ew_Ereg_nat regs1 [] 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; exact HRr).
  unfold e01_call_facts, e01b_env.
  cbn [e_S e_R e_F e_len e_cap e_null e_src e_left].
  split; [exact HJ1|]. split; [exact Eab|].
  split; [split; [exact ES | split; [exact ER | exact EF]]|].
  split; [eapply e01b_reg; [exact HS | reflexivity]|].
  split; [eapply e01b_reg; [exact HS|]; eapply e01b_at;
          [rewrite (ew_Ereg_nat regs1 [] 2 2%bv eq_refl); exact R2 | exact HRr]|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 [] 3%bv 3 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(lia)); exact R3|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 [] 4%bv 4 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(lia)); exact R4|].
  split; [eapply e01b_reg; [exact HS|]; rewrite E01_pp_size; reflexivity|].
  split.
  { unfold hd_cut. cbn [tl hi_L1 headamp_himg_A].
    repeat (apply Forall_cons; [cbn [fst snd hd_at hd_xv e_S e_R e_F e_len e_cap e_null e_src e_left]|]);
      [ | | | | | | | | | | | | apply Forall_nil ].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 8 8%bv eq_refl); exact R8 | exact HSr].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 9 9%bv eq_refl); exact R9 | exact HRr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 19 19%bv eq_refl); exact R19 | exact HShr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS | reflexivity].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 22 22%bv eq_refl); exact R22 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 23 23%bv eq_refl); exact R23 | exact HSHr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 26 26%bv eq_refl); exact R26 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 [] 27 27%bv eq_refl); rewrite R27, Hpe; reflexivity
      | revert HAE; clear; unfold kLowMemEnd; intros; lia].
    - rewrite (Z.mod_small 0 (2 ^ 64)) by (clear; lia).
      apply (e01b_cell _ _ 9%nat (e_R e) _ 0x40 0x48 0x40 0x48 0x40 (SLit 0) 0 RG U9);
      [ cbn [In]; left; reflexivity | reflexivity | clear; lia ]. }
  split.
  { apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) (ms_mem ms) (e_F e) headamp_A_shA HFSH).
    intros i Hi. cbn [length headamp_A_shA] in Hi. apply KEEP;
      [revert Hi HShr HKSH HKS HSr; clear; intros; lia | revert Hi HKSH; clear; intros; lia]. }
  split.
  { apply (e01b_kept_keep _ pos _ W1 mem1 (ms_mem ms) regs1 (ms_regs ms) (e_R e + 0x40) (e_R e + 0x48));
    [ apply (hq_kept_env rsegs hx pos e _ W1 mem1 regs1); [reflexivity | reflexivity | exact HKEPT]
    | intros x Hx Hn'; exact (KEEP x Hx Hn')
    | cbn [e_S]; exact HS80 | cbn [e_S]; revert HSr; clear; intros; lia
    | cbn [e_F]; revert HFrng; clear; intros; lia | cbn [e_F]; exact HFf
    | cbn [e_S]; left; exact HKS | cbn [e_F]; right; exact HKF ]. }
  apply (e01b_in_0 B _ W1 (ms_mem ms) (e_S e) (e_R e) (e_F e) A_EMPTY);
    [exact Hpl0 | exact (proj1 HAE) | exact (proj2 HAE)].
- (* ================= n = 1: the shadow byte is 1, the `bne` 0x80e28 is taken ================= *)
  assert (Hn26 : 0 < n < 2 ^ 26) by (destruct Hpn as [[Hz _] | [Hq _]]; [lia | exact Hq]).
  assert (Hin0 : In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)))
    by (destruct Hpn as [[Hz _] | [_ Hq]]; [lia | exact Hq]).
  assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by (rewrite Eab; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR1 Hin1) as (Hp16 & Hp4096 & Hpc & Happ & _ & _ & Hnmx).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  rewrite Hrq in Hpc, Happ.
  assert (Hp8 : p mod 8 = 0).
  { pose proof (Z.div_mod p 16 ltac:(lia)) as D16. rewrite Hp16, Z.add_0_r in D16.
    replace p with (2 * (p / 16) * 8) by lia. apply Z_mod_mult. }
  assert (Hp64 : 0 <= p < 2 ^ 64) by (revert Hp4096 Hpc Hcl Hn26; clear; intros; lia).
  assert (KB : forall i, 0 <= i < n ->
    aview rsegs (w_H W1) mem1 (p + i) = aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx) (p + i)).
  { intros i Hi. apply (Kblk1 p n i Hin0 Hin1); [rewrite Hrq; exact Hi | apply inFP_nil]. }
  destruct pl as [|b0 [|b1 rest]]; [cbn [length] in Hnl; lia | | cbn [length] in Hnl; lia].
  cbn [hd_zbytes map] in Hpl.
  destruct (Hpl 0%nat ltac:(cbn [length]; lia)) as [VM0e Rb0]. cbn [nth] in VM0e, Rb0.
  change (Z.of_nat 0) with 0 in VM0e.
  assert (A0 : aview rsegs (w_H W1) mem1 (p + 0) = Some (bv_unsigned b0)).
  { rewrite (KB 0 ltac:(lia)). apply hm_val1_aview; [exact VM0e | exact Rb0]. }
  rewrite Z.add_0_r in A0.
  destruct (hm_aview_val1 rsegs (w_H W1) mem1 p (bv_unsigned b0) A0) as [VM0 _].
  assert (Hland : 0 <= Z.land (bv_unsigned b0) 1 <= 1) by (apply e01b_land1; lia).
  (* the shadow byte of the input is its one partial granule *)
  assert (ASH : aview rsegs (w_H W1) mem1 (shadow_of_addr SHADOW_OFF p) = Some 1).
  { pose proof (hm_blk_shadow rsegs B ly1 S1 W1 mem1 md1 p n 0 HAR1 Hin1
      ltac:(rewrite Hrq; split; [lia|]; apply Z.div_str_pos; lia)) as HB.
    rewrite Z.add_0_r in HB. rewrite HB, Hrq, Hc. reflexivity. }
  (* the atoms of the start state *)
  assert (E27 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0)) 27 = w64 p)
    by (rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl); exact R27).
  assert (E23 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0)) 23
    = w64 SHADOW_OFF) by (rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23).
  assert (E32 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0)) 32
    = w64 (SHADOW_OFF + p / 8)) by (rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
  assert (E33 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0)) 33
    = w64 (bv_unsigned b0)) by (rewrite (ew_Ereg_extra regs1 _ 1); reflexivity).
  assert (RGsh : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0))
    (mrestrict (w_H W1) mem1) (e01b_sh (SLit 1))).
  { apply (hm_cell_region rsegs _ (w_H W1) mem1 32 (shadow_of_addr SHADOW_OFF p) 1 (SLit 1));
    [ rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth e01b_extra]; unfold w64; apply unsigned_lit_small;
      revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia
    | exact ASH | reflexivity
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8) by (apply Z.div_pos; lia); lia
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia); lia ]. }
  assert (RGd : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0))
    (mrestrict (w_H W1) mem1) (e01b_dat 1 e01b_cs1)).
  { apply (hm_ro_region rsegs _ (w_H W1) mem1 27 p 0 1 e01b_cs1);
    [ rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia
    | revert Hp64; clear; intros; lia | revert Hp64; clear; intros; lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ p 0 1 (SOff 33 0) (bv_unsigned b0));
    [ apply (e01b_at _ 33 (bv_unsigned b0) E33); revert Rb0; clear; intros; lia
    | cbn; revert Rb0; clear; intros; lia | cbn; lia | rewrite Z.add_0_r; exact VM0 ]. }
  pose proof (e01b_entryN W1 regs1 mem1 (e_R e) p (shadow_of_addr SHADOW_OFF p)
    (bv_unsigned b0) 0 1 e01b_cs1 [] sr_atoms (SLit 1) [E01B_ASH0; E01B_AND0]
    (regs_ok_Ereg regs1 _) R9 R27 HR0 HR48 HRac HP40 RGsh RGd
    ltac:(vm_compute; reflexivity) eq_refl Hp4096 Hp16 ltac:(clear; lia)
    ltac:(rewrite <- Hc; exact Hpc) ltac:(rewrite <- Hc; exact Happ)
    ltac:(revert Rb0; clear; intros; lia) ltac:(clear; lia) I) as HE.
  assert (HS : st_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0))
    (mkSS E01_HDR sr_atoms [E01B_R40; e01b_sh (SLit 1); e01b_dat 1 e01b_cs1] None
       (mkFacts (e01b_atoms []) [] [E01B_ASH0; E01B_AND0]))
    (restrict (w_H W1) (mkst regs1 (w64 E01_HDR) mem1 (seg_rom rsegs)))).
  { apply HE. unfold E01B_ASH0, E01B_AND0. split; [|split; [|exact I]].
    - apply (shadow_decl_ok _ 27 23 32 p SHADOW_OFF); [exact E27 | lia | exact E23 | exact E32].
    - apply (e01b_and7 _ 27 p 0 E27); revert Hp64 Hp8 Hpc Hn26 Hcl; clear; intros; lia. }
  clear HE.
  assert (R18' : getr (ms_regs (restrict (w_H W1) (mkst regs1 (w64 E01_HDR) mem1 (seg_rom rsegs)))) 18%bv
    = Z_to_bv 64 1) by (cbn [ms_regs restrict mkst]; rewrite R18, Hc; reflexivity).
  pose proof (st_ok_pin_lit rsegs _ _ _ 18%bv 1 HS ltac:(vm_compute; reflexivity) R18') as HS1.
  clear HS R18'. rename HS1 into HS. cbn [ss_pc ss_mem ss_resv ss_facts ss_regs] in HS.
  unfold cfg_at.
  aj_run_to E01_TBL_ok HS HJ1 E01_MALLOC.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0' bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (e_R e - e_S e));
    [ reflexivity
    | rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
      rewrite unsigned_lit_small by (revert HRr; clear; intros; lia); rewrite ES; lia
    | cbn; revert HRlo HSTK HASTK; clear; intros; lia | cbn; revert HKS; clear; intros; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (e_R e + 0x40 <= x < e_R e + 0x48) ->
    aview rsegs (w_H W1) (ms_mem ms) x = aview rsegs (w_H W1) mem1 x).
  { apply (e01b_keep _ _ _ _ _ _ HFr).
    intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<- | [<- | [<- | []]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    - rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9 in Ha. unfold w64 in Ha.
      rewrite unsigned_lit_small in Ha by (revert HRr; clear; intros; lia).
      revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl). cbn [ss_pc].
  apply SRr_ret.
  exists pos, (e01b_env (e_S e) (e_R e) (e_F e) (p + 1) 0 0 (Z.land (bv_unsigned b0) 1) []),
         ([] : list byte), ly1, S1, (ms_regs ms), (ms_mem ms).
  eexists. split; [reflexivity|].
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RG.
  assert (U9 : bv_unsigned (ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) 0)) 9)
    = e_R e) by (rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
                 apply unsigned_lit_small; revert HRr; clear; intros; lia).
  unfold e01_call_facts, e01b_env.
  cbn [e_S e_R e_F e_len e_cap e_null e_src e_left].
  split; [exact HJ1|]. split; [exact Eab|].
  split; [split; [exact ES | split; [exact ER | exact EF]]|].
  split; [eapply e01b_reg; [exact HS | reflexivity]|].
  split; [eapply e01b_reg; [exact HS|]; eapply e01b_at;
          [rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact R2 | exact HRr]|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 3%bv 3 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R3|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 4%bv 4 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R4|].
  split; [eapply e01b_reg; [exact HS|]; rewrite E01_pp_size; reflexivity|].
  split.
  { unfold hd_cut. cbn [tl hi_L1 headamp_himg_A].
    repeat (apply Forall_cons; [cbn [fst snd hd_at hd_xv e_S e_R e_F e_len e_cap e_null e_src e_left]|]);
      [ | | | | | | | | | | | | apply Forall_nil ].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact R8 | exact HSr].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl); exact R9 | exact HRr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19 | exact HShr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS | reflexivity].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23 | exact HSHr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl); exact R26 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply (e01b_off _ 27 1 p);
      [exact E27 | revert Hp64; clear; intros; lia
      | revert Hp64 Hpc Hcl Hn26; clear; intros; lia | reflexivity].
    - rewrite Z.mod_small by (revert Hland; clear; intros; lia).
      apply (e01b_cell _ _ 9%nat (e_R e) _ 0x40 0x48 0x40 0x48 0x40
               (SAlu ALU_AND (SOff 33 0) (SLit 1)) (Z.land (bv_unsigned b0) 1) RG U9);
      [ cbn [In]; left; reflexivity
      | apply (e01b_null _ 33 (bv_unsigned b0)); [exact E33 | revert Rb0; clear; intros; lia]
      | revert Hland; clear; intros; lia ]. }
  split.
  { apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) (ms_mem ms) (e_F e) headamp_A_shA HFSH).
    intros i Hi. cbn [length headamp_A_shA] in Hi. apply KEEP;
      [revert Hi HShr HKSH HKS HSr; clear; intros; lia | revert Hi HKSH; clear; intros; lia]. }
  split.
  { apply (e01b_kept_keep _ pos _ W1 mem1 (ms_mem ms) regs1 (ms_regs ms) (e_R e + 0x40) (e_R e + 0x48));
    [ apply (hq_kept_env rsegs hx pos e _ W1 mem1 regs1); [reflexivity | reflexivity | exact HKEPT]
    | intros x Hx Hn'; exact (KEEP x Hx Hn')
    | cbn [e_S]; exact HS80 | cbn [e_S]; revert HSr; clear; intros; lia
    | cbn [e_F]; revert HFrng; clear; intros; lia | cbn [e_F]; exact HFf
    | cbn [e_S]; left; exact HKS | cbn [e_F]; right; exact HKF ]. }
  apply (e01b_in_1 B _ W1 (ms_mem ms) (e_S e) (e_R e) (e_F e) p b0);
    [ exact (eq_sym Epl) | exact Hp4096 | rewrite <- Hc; exact Hpc | rewrite <- Hc; exact Happ ].
- (* ================= 2 <= n <= 7: the shadow byte is n, both checks take their slow block ================= *)
  assert (Hn26 : 0 < n < 2 ^ 26) by (destruct Hpn as [[Hz _] | [Hq _]]; [lia | exact Hq]).
  assert (Hin0 : In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)))
    by (destruct Hpn as [[Hz _] | [_ Hq]]; [lia | exact Hq]).
  assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by (rewrite Eab; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR1 Hin1) as (Hp16 & Hp4096 & Hpc & Happ & _ & _ & Hnmx).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  rewrite Hrq in Hpc, Happ.
  assert (Hp8 : p mod 8 = 0).
  { pose proof (Z.div_mod p 16 ltac:(lia)) as D16. rewrite Hp16, Z.add_0_r in D16.
    replace p with (2 * (p / 16) * 8) by lia. apply Z_mod_mult. }
  assert (Hp64 : 0 <= p < 2 ^ 64) by (revert Hp4096 Hpc Hcl Hn26; clear; intros; lia).
  assert (KB : forall i, 0 <= i < n ->
    aview rsegs (w_H W1) mem1 (p + i) = aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx) (p + i)).
  { intros i Hi. apply (Kblk1 p n i Hin0 Hin1); [rewrite Hrq; exact Hi | apply inFP_nil]. }
  destruct pl as [|b0 [|b1 rest]];
    [cbn [length] in Hnl; lia | cbn [length] in Hnl; lia |].
  cbn [hd_zbytes map] in Hpl.
  destruct (Hpl 0%nat ltac:(cbn [length]; lia)) as [VM0e Rb0]. cbn [nth] in VM0e, Rb0.
  change (Z.of_nat 0) with 0 in VM0e.
  destruct (Hpl 1%nat ltac:(cbn [length]; lia)) as [VM1e Rb1]. cbn [nth] in VM1e, Rb1.
  change (Z.of_nat 1) with 1 in VM1e.
  assert (A0 : aview rsegs (w_H W1) mem1 (p + 0) = Some (bv_unsigned b0)).
  { rewrite (KB 0 ltac:(lia)). apply hm_val1_aview; [exact VM0e | exact Rb0]. }
  rewrite Z.add_0_r in A0.
  assert (A1 : aview rsegs (w_H W1) mem1 (p + 1) = Some (bv_unsigned b1)).
  { rewrite (KB 1 ltac:(lia)). apply hm_val1_aview; [exact VM1e | exact Rb1]. }
  destruct (hm_aview_val1 rsegs (w_H W1) mem1 p (bv_unsigned b0) A0) as [VM0 _].
  destruct (hm_aview_val1 rsegs (w_H W1) mem1 (p + 1) (bv_unsigned b1) A1) as [VM1 _].
  assert (Hland : 0 <= Z.land (bv_unsigned b0) 1 <= 1) by (apply e01b_land1; lia).
  assert (Hcap : 0 <= bv_unsigned b1 mod 10 <= 9)
    by (pose proof (Z.mod_pos_bound (bv_unsigned b1) 10 ltac:(lia)); lia).
  assert (ASH : aview rsegs (w_H W1) mem1 (shadow_of_addr SHADOW_OFF p) = Some n).
  { pose proof (hm_blk_shadow rsegs B ly1 S1 W1 mem1 md1 p n 0 HAR1 Hin1
      ltac:(rewrite Hrq; split; [lia|]; apply Z.div_str_pos; lia)) as HB.
    rewrite Z.add_0_r in HB. rewrite HB, Hrq, (Z.div_small n 8) by lia.
    rewrite (Z.mod_small n 8) by lia. reflexivity. }
  assert (E27 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 27 = w64 p)
    by (rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl); exact R27).
  assert (E23 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 23 = w64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23).
  assert (E32 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 32 = w64 (SHADOW_OFF + p / 8))
    by (rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
  assert (E33 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 33 = w64 (bv_unsigned b0))
    by (rewrite (ew_Ereg_extra regs1 _ 1); reflexivity).
  assert (E34 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 34 = w64 (bv_unsigned b1))
    by (rewrite (ew_Ereg_extra regs1 _ 2); reflexivity).
  assert (E18n : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 18 = w64 n)
    by (rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl); exact R18).
  assert (RGsh : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mrestrict (w_H W1) mem1) (e01b_sh (SOff 18 0))).
  { apply (hm_cell_region rsegs _ (w_H W1) mem1 32 (shadow_of_addr SHADOW_OFF p) n (SOff 18 0));
    [ rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth e01b_extra]; unfold w64; apply unsigned_lit_small;
      revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia
    | exact ASH | apply (e01b_at _ 18 n E18n); revert Hn26; clear; intros; lia
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8) by (apply Z.div_pos; lia); lia
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia); lia ]. }
  assert (RGd : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mrestrict (w_H W1) mem1) (e01b_dat 2 e01b_cs2)).
  { apply (hm_ro_region rsegs _ (w_H W1) mem1 27 p 0 2 e01b_cs2);
    [ rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia
    | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hcl Hn26; clear; intros; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (chunk_ok_val rsegs _ _ p 0 1 (SOff 33 0) (bv_unsigned b0));
      [ apply (e01b_at _ 33 (bv_unsigned b0) E33); revert Rb0; clear; intros; lia
      | cbn; revert Rb0; clear; intros; lia | cbn; lia | rewrite Z.add_0_r; exact VM0 ].
    - apply (chunk_ok_val rsegs _ _ p 1 1 (SOff 34 0) (bv_unsigned b1));
      [ apply (e01b_at _ 34 (bv_unsigned b1) E34); revert Rb1; clear; intros; lia
      | cbn; revert Rb1; clear; intros; lia | cbn; lia | exact VM1 ]. }
  pose proof (e01b_entryN W1 regs1 mem1 (e_R e) p (shadow_of_addr SHADOW_OFF p)
    (bv_unsigned b0) (bv_unsigned b1) 2 e01b_cs2 [(18%nat, mkAF 2 7 0)] sr_atoms (SOff 18 0) [E01B_ASH0; E01B_ASH1; E01B_AND0; E01B_AND1]
    (regs_ok_Ereg regs1 _) R9 R27 HR0 HR48 HRac HP40 RGsh RGd
    ltac:(vm_compute; reflexivity) eq_refl Hp4096 Hp16 ltac:(clear; lia)
    ltac:(revert Hpc Hc; clear; intros; lia)
    ltac:(apply (in_app_sub p n p 2 Happ); [clear; lia | clear; lia | revert Hc; clear; intros; lia])
    ltac:(revert Rb0; clear; intros; lia) ltac:(revert Rb1; clear; intros; lia)) as HE.
  assert (HS : st_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mkSS E01_HDR sr_atoms [E01B_R40; e01b_sh (SOff 18 0); e01b_dat 2 e01b_cs2] None
       (mkFacts (e01b_atoms [(18%nat, mkAF 2 7 0)]) [] [E01B_ASH0; E01B_ASH1; E01B_AND0; E01B_AND1]))
    (restrict (w_H W1) (mkst regs1 (w64 E01_HDR) mem1 (seg_rom rsegs)))).
  { apply HE.
    - split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18n. unfold w64. rewrite unsigned_lit_small by (revert Hn26; clear; intros; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    - unfold E01B_ASH0, E01B_ASH1, E01B_AND0, E01B_AND1. split; [|split; [|split; [|split; [|exact I]]]].
      + apply (shadow_decl_ok _ 27 23 32 p SHADOW_OFF); [exact E27 | lia | exact E23 | exact E32].
      + apply (e01b_ash1 _ 27 23 32 p SHADOW_OFF);
        [ exact E27 | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hn26 Hcl; clear; intros; lia
        | exact Hp8 | exact E23 | revert HSHr; clear; unfold SHADOW_OFF; intros; lia
        | revert Hp64 Hpc Hn26 Hcl; clear; unfold SHADOW_OFF; intros;
          assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia
        | exact E32 ].
      + apply (e01b_and7 _ 27 p 0 E27); revert Hp64 Hp8 Hpc Hn26 Hcl; clear; intros; lia.
      + apply (e01b_and7 _ 27 p 1 E27); revert Hp64 Hp8 Hpc Hn26 Hcl; clear; intros; lia. }
  clear HE.
  unfold cfg_at.
  aj_run_to E01_TBL_ok HS HJ1 E01_MALLOC.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0' bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (e_R e - e_S e));
    [ reflexivity
    | rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
      rewrite unsigned_lit_small by (revert HRr; clear; intros; lia); rewrite ES; lia
    | cbn; revert HRlo HSTK HASTK; clear; intros; lia | cbn; revert HKS; clear; intros; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (e_R e + 0x40 <= x < e_R e + 0x48) ->
    aview rsegs (w_H W1) (ms_mem ms) x = aview rsegs (w_H W1) mem1 x).
  { apply (e01b_keep _ _ _ _ _ _ HFr).
    intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<- | [<- | [<- | []]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    - rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9 in Ha. unfold w64 in Ha.
      rewrite unsigned_lit_small in Ha by (revert HRr; clear; intros; lia).
      revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl). cbn [ss_pc].
  apply SRr_ret.
  exists pos, (e01b_env (e_S e) (e_R e) (e_F e) (p + 2) (n - 2) (bv_unsigned b1 mod 10)
                 (Z.land (bv_unsigned b0) 1) rest), rest, ly1, S1, (ms_regs ms), (ms_mem ms).
  eexists. split; [reflexivity|].
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RG.
  assert (U9 : bv_unsigned (ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 9) = e_R e)
    by (rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
        apply unsigned_lit_small; revert HRr; clear; intros; lia).
  unfold e01_call_facts, e01b_env.
  cbn [e_S e_R e_F e_len e_cap e_null e_src e_left].
  split; [exact HJ1|]. split; [exact Eab|].
  split; [split; [exact ES | split; [exact ER | exact EF]]|].
  split; [eapply e01b_reg; [exact HS | reflexivity]|].
  split; [eapply e01b_reg; [exact HS|]; eapply e01b_at;
          [rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact R2 | exact HRr]|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 3%bv 3 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R3|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 4%bv 4 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R4|].
  split; [eapply e01b_reg; [exact HS|]; rewrite E01_pp_size; reflexivity|].
  split.
  { unfold hd_cut. cbn [tl hi_L1 headamp_himg_A].
    repeat (apply Forall_cons; [cbn [fst snd hd_at hd_xv e_S e_R e_F e_len e_cap e_null e_src e_left]|]);
      [ | | | | | | | | | | | | apply Forall_nil ].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact R8 | exact HSr].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl); exact R9 | exact HRr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19 | exact HShr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply (e01b_off _ 18 (-2) n);
      [ exact E18n | revert Hn26; clear; intros; lia | revert Hn26 Hc; clear; intros; lia
      | reflexivity ].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23 | exact HSHr].
    - eapply e01b_reg; [exact HS|]; apply (e01b_cap _ 34 (bv_unsigned b1));
      [exact E34 | revert Rb1; clear; intros; lia].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl); exact R26 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply (e01b_off _ 27 2 p);
      [exact E27 | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hcl Hn26; clear; intros; lia
      | reflexivity].
    - rewrite Z.mod_small by (revert Hland; clear; intros; lia).
      apply (e01b_cell _ _ 9%nat (e_R e) _ 0x40 0x48 0x40 0x48 0x40
               (SAlu ALU_AND (SOff 33 0) (SLit 1)) (Z.land (bv_unsigned b0) 1) RG U9);
      [ cbn [In]; left; reflexivity
      | apply (e01b_null _ 33 (bv_unsigned b0)); [exact E33 | revert Rb0; clear; intros; lia]
      | revert Hland; clear; intros; lia ]. }
  split.
  { apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) (ms_mem ms) (e_F e) headamp_A_shA HFSH).
    intros i Hi. cbn [length headamp_A_shA] in Hi. apply KEEP;
      [revert Hi HShr HKSH HKS HSr; clear; intros; lia | revert Hi HKSH; clear; intros; lia]. }
  split.
  { apply (e01b_kept_keep _ pos _ W1 mem1 (ms_mem ms) regs1 (ms_regs ms) (e_R e + 0x40) (e_R e + 0x48));
    [ apply (hq_kept_env rsegs hx pos e _ W1 mem1 regs1); [reflexivity | reflexivity | exact HKEPT]
    | intros x Hx Hn'; exact (KEEP x Hx Hn')
    | cbn [e_S]; exact HS80 | cbn [e_S]; revert HSr; clear; intros; lia
    | cbn [e_F]; revert HFrng; clear; intros; lia | cbn [e_F]; exact HFf
    | cbn [e_S]; left; exact HKS | cbn [e_F]; right; exact HKF ]. }
  apply (e01b_in_2 B _ W1 (ms_mem ms) (e_S e) (e_R e) (e_F e) p n b0 b1 rest);
    [ exact (eq_sym Epl) | exact Hnl | exact Hin0 | exact Hp4096
    | rewrite Hrq; exact Hpc | rewrite Hrq; exact Happ |].
  apply (e01b_garr8_keep (w_H (h_W rsegs hx)) (w_H W1) (h_mem rsegs hx) (ms_mem ms)
           (p + 2) (hd_zbytes rest));
  [ exact (e01b_garr8_tl2 _ p (bv_unsigned b0) (bv_unsigned b1) (hd_zbytes rest) Hpl) |].
  intros j Hj.
  assert (Hjr : (j < length rest)%nat)
    by (unfold hd_zbytes in Hj; rewrite length_map in Hj; exact Hj).
  assert (Hjn : 0 <= 2 + Z.of_nat j < n) by (cbn [length] in Hnl; lia).
  replace (p + 2 + Z.of_nat j) with (p + (2 + Z.of_nat j)) by lia.
  rewrite (KEEP (p + (2 + Z.of_nat j))
    ltac:(revert Hjn Hp64 Hpc Hcl; clear; intros; lia)
    ltac:(revert Hjn Hp4096 Hpc HRac Hcl; clear; intros; lia)).
  exact (KB (2 + Z.of_nat j) Hjn).
- (* ================= n >= 8: the shadow byte is 0, both checks pass at once ================= *)
  assert (Hn26 : 0 < n < 2 ^ 26) by (destruct Hpn as [[Hz _] | [Hq _]]; [lia | exact Hq]).
  assert (Hin0 : In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)))
    by (destruct Hpn as [[Hz _] | [_ Hq]]; [lia | exact Hq]).
  assert (Hin1 : In (p, n) (ablocks B ly1 S1)) by (rewrite Eab; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR1 Hin1) as (Hp16 & Hp4096 & Hpc & Happ & _ & _ & Hnmx).
  assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  rewrite Hrq in Hpc, Happ.
  assert (Hp8 : p mod 8 = 0).
  { pose proof (Z.div_mod p 16 ltac:(lia)) as D16. rewrite Hp16, Z.add_0_r in D16.
    replace p with (2 * (p / 16) * 8) by lia. apply Z_mod_mult. }
  assert (Hp64 : 0 <= p < 2 ^ 64) by (revert Hp4096 Hpc Hcl Hn26; clear; intros; lia).
  assert (KB : forall i, 0 <= i < n ->
    aview rsegs (w_H W1) mem1 (p + i) = aview rsegs (w_H (h_W rsegs hx)) (h_mem rsegs hx) (p + i)).
  { intros i Hi. apply (Kblk1 p n i Hin0 Hin1); [rewrite Hrq; exact Hi | apply inFP_nil]. }
  destruct pl as [|b0 [|b1 rest]];
    [cbn [length] in Hnl; lia | cbn [length] in Hnl; lia |].
  cbn [hd_zbytes map] in Hpl.
  destruct (Hpl 0%nat ltac:(cbn [length]; lia)) as [VM0e Rb0]. cbn [nth] in VM0e, Rb0.
  change (Z.of_nat 0) with 0 in VM0e.
  destruct (Hpl 1%nat ltac:(cbn [length]; lia)) as [VM1e Rb1]. cbn [nth] in VM1e, Rb1.
  change (Z.of_nat 1) with 1 in VM1e.
  assert (A0 : aview rsegs (w_H W1) mem1 (p + 0) = Some (bv_unsigned b0)).
  { rewrite (KB 0 ltac:(lia)). apply hm_val1_aview; [exact VM0e | exact Rb0]. }
  rewrite Z.add_0_r in A0.
  assert (A1 : aview rsegs (w_H W1) mem1 (p + 1) = Some (bv_unsigned b1)).
  { rewrite (KB 1 ltac:(lia)). apply hm_val1_aview; [exact VM1e | exact Rb1]. }
  destruct (hm_aview_val1 rsegs (w_H W1) mem1 p (bv_unsigned b0) A0) as [VM0 _].
  destruct (hm_aview_val1 rsegs (w_H W1) mem1 (p + 1) (bv_unsigned b1) A1) as [VM1 _].
  assert (Hland : 0 <= Z.land (bv_unsigned b0) 1 <= 1) by (apply e01b_land1; lia).
  assert (Hcap : 0 <= bv_unsigned b1 mod 10 <= 9)
    by (pose proof (Z.mod_pos_bound (bv_unsigned b1) 10 ltac:(lia)); lia).
  assert (ASH : aview rsegs (w_H W1) mem1 (shadow_of_addr SHADOW_OFF p) = Some 0).
  { pose proof (hm_blk_shadow rsegs B ly1 S1 W1 mem1 md1 p n 0 HAR1 Hin1
      ltac:(rewrite Hrq; split; [lia|]; apply Z.div_str_pos; lia)) as HB.
    rewrite Z.add_0_r in HB. rewrite HB, Hrq.
    assert (Hd8 : 0 < n / 8) by (apply Z.div_str_pos; lia).
    destruct (Z.ltb_spec 0 (n / 8)); [reflexivity | lia]. }
  assert (E27 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 27 = w64 p)
    by (rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl); exact R27).
  assert (E23 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 23 = w64 SHADOW_OFF)
    by (rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23).
  assert (E32 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 32 = w64 (SHADOW_OFF + p / 8))
    by (rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
  assert (E33 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 33 = w64 (bv_unsigned b0))
    by (rewrite (ew_Ereg_extra regs1 _ 1); reflexivity).
  assert (E34 : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 34 = w64 (bv_unsigned b1))
    by (rewrite (ew_Ereg_extra regs1 _ 2); reflexivity).
  assert (E18n : ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 18 = w64 n)
    by (rewrite (ew_Ereg_nat regs1 _ 18 18%bv eq_refl); exact R18).
  assert (RGsh : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mrestrict (w_H W1) mem1) (e01b_sh (SLit 0))).
  { apply (hm_cell_region rsegs _ (w_H W1) mem1 32 (shadow_of_addr SHADOW_OFF p) 0 (SLit 0));
    [ rewrite (ew_Ereg_extra regs1 _ 0); cbn [nth e01b_extra]; unfold w64; apply unsigned_lit_small;
      revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia
    | exact ASH | reflexivity
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (0 <= p / 8) by (apply Z.div_pos; lia); lia
    | revert Hp64 Hpc Hn26 Hcl; clear; unfold shadow_of_addr, SHADOW_OFF; intros;
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia); lia ]. }
  assert (RGd : region_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mrestrict (w_H W1) mem1) (e01b_dat 2 e01b_cs2)).
  { apply (hm_ro_region rsegs _ (w_H W1) mem1 27 p 0 2 e01b_cs2);
    [ rewrite (ew_Ereg_nat regs1 _ 27 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; lia
    | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hcl Hn26; clear; intros; lia |].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    - apply (chunk_ok_val rsegs _ _ p 0 1 (SOff 33 0) (bv_unsigned b0));
      [ apply (e01b_at _ 33 (bv_unsigned b0) E33); revert Rb0; clear; intros; lia
      | cbn; revert Rb0; clear; intros; lia | cbn; lia | rewrite Z.add_0_r; exact VM0 ].
    - apply (chunk_ok_val rsegs _ _ p 1 1 (SOff 34 0) (bv_unsigned b1));
      [ apply (e01b_at _ 34 (bv_unsigned b1) E34); revert Rb1; clear; intros; lia
      | cbn; revert Rb1; clear; intros; lia | cbn; lia | exact VM1 ]. }
  pose proof (e01b_entryN W1 regs1 mem1 (e_R e) p (shadow_of_addr SHADOW_OFF p)
    (bv_unsigned b0) (bv_unsigned b1) 2 e01b_cs2 [(18%nat, mkAF 8 (2 ^ 26 - 1) 0)] sr_atoms (SLit 0) [E01B_ASH0; E01B_ASH1]
    (regs_ok_Ereg regs1 _) R9 R27 HR0 HR48 HRac HP40 RGsh RGd
    ltac:(vm_compute; reflexivity) eq_refl Hp4096 Hp16 ltac:(clear; lia)
    ltac:(revert Hpc Hc; clear; intros; lia)
    ltac:(apply (in_app_sub p n p 2 Happ); [clear; lia | clear; lia | revert Hc; clear; intros; lia])
    ltac:(revert Rb0; clear; intros; lia) ltac:(revert Rb1; clear; intros; lia)) as HE.
  assert (HS : st_ok rsegs (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1)))
    (mkSS E01_HDR sr_atoms [E01B_R40; e01b_sh (SLit 0); e01b_dat 2 e01b_cs2] None
       (mkFacts (e01b_atoms [(18%nat, mkAF 8 (2 ^ 26 - 1) 0)]) [] [E01B_ASH0; E01B_ASH1]))
    (restrict (w_H W1) (mkst regs1 (w64 E01_HDR) mem1 (seg_rom rsegs)))).
  { apply HE.
    - split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18n. unfold w64. rewrite unsigned_lit_small by (revert Hn26; clear; intros; lia).
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
    - unfold E01B_ASH0, E01B_ASH1, E01B_AND0, E01B_AND1. split; [|split; [|exact I]].
      + apply (shadow_decl_ok _ 27 23 32 p SHADOW_OFF); [exact E27 | lia | exact E23 | exact E32].
      + apply (e01b_ash1 _ 27 23 32 p SHADOW_OFF);
        [ exact E27 | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hn26 Hcl; clear; intros; lia
        | exact Hp8 | exact E23 | revert HSHr; clear; unfold SHADOW_OFF; intros; lia
        | revert Hp64 Hpc Hn26 Hcl; clear; unfold SHADOW_OFF; intros;
          assert (0 <= p / 8 <= p) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia); lia
        | exact E32 ]. }
  clear HE.
  unfold cfg_at.
  aj_run_to E01_TBL_ok HS HJ1 E01_MALLOC.
  { lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0' ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0' bc ly own) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (e_R e - e_S e));
    [ reflexivity
    | rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
      rewrite unsigned_lit_small by (revert HRr; clear; intros; lia); rewrite ES; lia
    | cbn; revert HRlo HSTK HASTK; clear; intros; lia | cbn; revert HKS; clear; intros; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> ~ (e_R e + 0x40 <= x < e_R e + 0x48) ->
    aview rsegs (w_H W1) (ms_mem ms) x = aview rsegs (w_H W1) mem1 x).
  { apply (e01b_keep _ _ _ _ _ _ HFr).
    intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    destruct Hin as [<- | [<- | [<- | []]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    - rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9 in Ha. unfold w64 in Ha.
      rewrite unsigned_lit_small in Ha by (revert HRr; clear; intros; lia).
      revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia.
    - revert Ha; clear; intros; lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W1) _ _ ms HS eq_refl). cbn [ss_pc].
  apply SRr_ret.
  exists pos, (e01b_env (e_S e) (e_R e) (e_F e) (p + 2) (n - 2) (bv_unsigned b1 mod 10)
                 (Z.land (bv_unsigned b0) 1) rest), rest, ly1, S1, (ms_regs ms), (ms_mem ms).
  eexists. split; [reflexivity|].
  pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as RG.
  assert (U9 : bv_unsigned (ew (Ereg regs1 (e01b_extra (shadow_of_addr SHADOW_OFF p) (bv_unsigned b0) (bv_unsigned b1))) 9) = e_R e)
    by (rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl), R9; unfold w64;
        apply unsigned_lit_small; revert HRr; clear; intros; lia).
  unfold e01_call_facts, e01b_env.
  cbn [e_S e_R e_F e_len e_cap e_null e_src e_left].
  split; [exact HJ1|]. split; [exact Eab|].
  split; [split; [exact ES | split; [exact ER | exact EF]]|].
  split; [eapply e01b_reg; [exact HS | reflexivity]|].
  split; [eapply e01b_reg; [exact HS|]; eapply e01b_at;
          [rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); exact R2 | exact HRr]|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 3%bv 3 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R3|].
  split; [rewrite (e01b_keepreg (w_H W1) _ _ ms regs1 _ 4%bv 4 HS eq_refl
            ltac:(vm_compute; reflexivity) ltac:(clear; lia)); exact R4|].
  split; [eapply e01b_reg; [exact HS|]; rewrite E01_pp_size; reflexivity|].
  split.
  { unfold hd_cut. cbn [tl hi_L1 headamp_himg_A].
    repeat (apply Forall_cons; [cbn [fst snd hd_at hd_xv e_S e_R e_F e_len e_cap e_null e_src e_left]|]);
      [ | | | | | | | | | | | | apply Forall_nil ].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 8 8%bv eq_refl); exact R8 | exact HSr].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 9 9%bv eq_refl); exact R9 | exact HRr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19 | exact HShr].
    - eapply e01b_reg; [exact HS | reflexivity].
    - eapply e01b_reg; [exact HS|]; eapply (e01b_off _ 18 (-2) n);
      [ exact E18n | revert Hn26; clear; intros; lia | revert Hn26 Hc; clear; intros; lia
      | reflexivity ].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 22 22%bv eq_refl); exact R22 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 23 23%bv eq_refl); exact R23 | exact HSHr].
    - eapply e01b_reg; [exact HS|]; apply (e01b_cap _ 34 (bv_unsigned b1));
      [exact E34 | revert Rb1; clear; intros; lia].
    - rewrite Z.add_0_r. eapply e01b_reg; [exact HS|]; eapply e01b_at;
      [rewrite (ew_Ereg_nat regs1 _ 26 26%bv eq_refl); exact R26 | exact HFrng].
    - eapply e01b_reg; [exact HS|]; eapply (e01b_off _ 27 2 p);
      [exact E27 | revert Hp64; clear; intros; lia | revert Hp64 Hpc Hcl Hn26; clear; intros; lia
      | reflexivity].
    - rewrite Z.mod_small by (revert Hland; clear; intros; lia).
      apply (e01b_cell _ _ 9%nat (e_R e) _ 0x40 0x48 0x40 0x48 0x40
               (SAlu ALU_AND (SOff 33 0) (SLit 1)) (Z.land (bv_unsigned b0) 1) RG U9);
      [ cbn [In]; left; reflexivity
      | apply (e01b_null _ 33 (bv_unsigned b0)); [exact E33 | revert Rb0; clear; intros; lia]
      | revert Hland; clear; intros; lia ]. }
  split.
  { apply (hm_fsh_kept rsegs (w_H W1) mem1 (w_H W1) (ms_mem ms) (e_F e) headamp_A_shA HFSH).
    intros i Hi. cbn [length headamp_A_shA] in Hi. apply KEEP;
      [revert Hi HShr HKSH HKS HSr; clear; intros; lia | revert Hi HKSH; clear; intros; lia]. }
  split.
  { apply (e01b_kept_keep _ pos _ W1 mem1 (ms_mem ms) regs1 (ms_regs ms) (e_R e + 0x40) (e_R e + 0x48));
    [ apply (hq_kept_env rsegs hx pos e _ W1 mem1 regs1); [reflexivity | reflexivity | exact HKEPT]
    | intros x Hx Hn'; exact (KEEP x Hx Hn')
    | cbn [e_S]; exact HS80 | cbn [e_S]; revert HSr; clear; intros; lia
    | cbn [e_F]; revert HFrng; clear; intros; lia | cbn [e_F]; exact HFf
    | cbn [e_S]; left; exact HKS | cbn [e_F]; right; exact HKF ]. }
  apply (e01b_in_2 B _ W1 (ms_mem ms) (e_S e) (e_R e) (e_F e) p n b0 b1 rest);
    [ exact (eq_sym Epl) | exact Hnl | exact Hin0 | exact Hp4096
    | rewrite Hrq; exact Hpc | rewrite Hrq; exact Happ |].
  apply (e01b_garr8_keep (w_H (h_W rsegs hx)) (w_H W1) (h_mem rsegs hx) (ms_mem ms)
           (p + 2) (hd_zbytes rest));
  [ exact (e01b_garr8_tl2 _ p (bv_unsigned b0) (bv_unsigned b1) (hd_zbytes rest) Hpl) |].
  intros j Hj.
  assert (Hjr : (j < length rest)%nat)
    by (unfold hd_zbytes in Hj; rewrite length_map in Hj; exact Hj).
  assert (Hjn : 0 <= 2 + Z.of_nat j < n) by (cbn [length] in Hnl; lia).
  replace (p + 2 + Z.of_nat j) with (p + (2 + Z.of_nat j)) by lia.
  rewrite (KEEP (p + (2 + Z.of_nat j))
    ltac:(revert Hjn Hp64 Hpc Hcl; clear; intros; lia)
    ltac:(revert Hjn Hp4096 Hpc HRac Hcl; clear; intros; lia)).
  exact (KB (2 + Z.of_nat j) Hjn).
Qed.
End s.

Print Assumptions e01_body_ok.
