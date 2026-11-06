(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01P.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's code 0x807e0 .. 0x809bc and its pcs; the class-4 frame (1024 bytes, 128 shadow
   bytes, the flag pointer word at F + 0x3f8); the real frame's cell R + 0x190; F in s9 (x25), the shadow address in
   s3 (x19), the shadow offset in s4 (x20, the alias fact's register), the size test in a3; the 88 shadow stores and
   rsb_P0; the records of lib/AU/RtPgSegB.v and lib/AU/RtPgE01DB.v; the stack bound 0x230. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): part PRO of the states
   segment S_E01 of the walk of LLVMFuzzerTestOneInput (lib/AU/RtPgE01DB.v e01b_pro_stmt), FR 0x807e0 -> HD 0x809bc.
   Proves no function (kind: segment lemma, one part).

   THE CODE (0x807e0 .. 0x809b4, 118 words, 110 of them walked; no load and no instrumented check)
     0x807e0  mv s8,a0                 a0 = F, the class-4 frame __asan_stack_malloc_4 returned
     0x807e4  j 0x807ec                (the arm 0x807e8 `li s8,0` is not walked)
     0x807ec  mv s9,s8
     0x807f0  bnez s8 -> 0x80810       taken: F >= 4096 (the real-stack arm 0x807f4 .. 0x8080c is not walked)
     0x80810  sd s9,400(s1)            R + 0x190 := F
     0x80814 .. 0x80838                a2 = 0x41b58ab3, a4 = 0x113f3, a5 = 0x8076c, s3 = s9 >> 3,
                                       a0 = -8, a3 = -15, a1 = -14
     0x8083c .. 0x80844                F[0] := a2, F[8] := a4, F[16] := a5 (the frame header)
     0x80848  li a2,-13                0x8084c  add s3,s3,s4   s3 = (F >> 3) + SHADOW_OFF = shadow_addr F
     0x80850 .. 0x809b0                the 88 `sb` of the frame's shadow at s3 + 0 .. s3 + 87, in a scrambled order
                                       (RtPgSegB.rsb_P0: 0xf1 0xf8 0xf2 0xf3 from a3 a0 a1 a2), with
                                       `srli a3,s5,0x1a` 0x80860 among them (after the four stores of a3 = -15)
     0x809b4  beqz a3 -> 0x809bc       taken: n < 2^26 (0x809b8 `j 0x83014` is not walked)

   THE PROOF. One run of the kit's symbolic engine under the harness journal (lib/Reusable/YCbq.v aj_run_to, with
   SRr_run_to_AJ's awr_ok obligation), from a state over Ereg regs [shadow_addr F] with three regions: the real
   frame's cell [R + 0x190, R + 0x198) at atom 9 (s1), the frame header [F, F + 24) at atom 10 (a0), and the frame's
   88 shadow bytes at the extra atom 32. The atom facts (numeral bounds only) decide both branches without a split:
   F in [4096, 0x7fffff800000 - 1024] decides `bnez s8`, and the condition fact (n >> 26) == 0 (n < 2^26) decides
   `beqz a3`; the alias fact ((a0 >> 3) + s4, atom 32) (YP0i shadow_decl_ok) turns `add s3,s3,s4` into the shadow
   region's base, so the 88 stores land in that region. The run stops at 0x809bc; the last state gives
   s3 = shadow_addr F, s8 = s9 = F and the other registers kept, the shadow region's 88 literal chunks give
   rt_fsh F rsb_P0, and every byte outside the three write windows is kept (the 13 saves, the flag pointer word
   F + 0x3f8, the input). Then the continuation e01b_from_hd is applied at 0x809bc. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import
RtPgImgB RtPgSegB RtPgE01DB RtPgMemB RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the engine's start state ======================================== *)
(* 0x807e0 .. 0x809bc *)
Definition e01pb_tbl : ctable := build_table rsegs E01B_FR 120 TEmpty.
Lemma e01pb_tbl_ok : table_ok rsegs e01pb_tbl.
Proof. apply build_table_ok0. unfold E01B_FR. lia. Qed.

(* the real frame's cell R + 0x190 (atom 9 = s1 = R), the frame header (atom 10 = a0 = F), the frame's shadow
   (atom 32 = the extra atom shadow_addr F) *)
Definition E01PB_R : YP09.region := YP09.mkRegion (Some 9%nat) 0x190 0x198 0x190 0x198 [].
Definition E01PB_F : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition E01PB_SH : YP09.region := YP09.mkRegion (Some 32%nat) 0 88 0 88 [].
(* atom 9 = R in [0x7fff7f800000, 2^47], 32-aligned; atom 10 = F in [4096, 0x7fffff800000 - 1024], 32-aligned;
   atom 21 = s5 = n < 2^26; the condition (n >> 26) == 0; the alias ((a0 >> 3) + s4, atom 32) *)
Definition e01pb_facts : facts :=
  mkFacts [ (9%nat, mkAF 0x7fff7f800000 0x800000000000 5); (10%nat, mkAF 4096 0x7fffff7ffc00 5);
            (21%nat, mkAF 0 0x3ffffff 0) ]
          [ mkAC BC_EQ (SAlu ALU_SRL (SOff 21 0) (SLit 26)) (SLit 0) ]
          [ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 20 0), SOff 32 0) ].
Definition e01pb_ss : sstate := mkSS E01B_FR sr_atoms [E01PB_R; E01PB_F; E01PB_SH] None e01pb_facts.

(* ======================================== helpers ======================================== *)
(* the shadow chunks: byte i of pat is a one-byte literal chunk at offset i *)
Definition e01pb_chk1 (cs : list YP09.chunk) (i : nat) (v : Z) : bool :=
  existsb (fun c => match c with
                    | YP09.mkChunk o (CVal w (SLit z)) => (o =? Z.of_nat i) && (w =? 1)%N && (z mod 256 =? v)
                    | _ => false
                    end) cs.
Definition e01pb_chk (cs : list YP09.chunk) (pat : list Z) : bool :=
  forallb (fun i => e01pb_chk1 cs i (nth i pat 0)) (seq 0 (length pat)).

(* n < 2^26, so n >> 26 = 0 (boxreg eb_srl26) *)
Lemma e01pb_srl26 : forall {fx : YK11.FPState} E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 26 ->
  U E (SAlu ALU_SRL (SOff k 0) (SLit 26)) = 0.
Proof.
intros fx E k v Hk Hv. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 26) 63) with 26.
rewrite (U_atom E k v Hk) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* a shadow address of a class-4 frame below the ceiling is no application byte *)
Lemma e01pb_sh_not_app : forall {rc : YM05.RunCeil} F lo len a,
  4096 <= F -> F + 1024 <= alloc_ceiling -> in_app lo len -> lo <= a < lo + len ->
  ~ (shadow_addr F <= a < shadow_addr F + 128).
Proof.
intros rc F lo len a H1 H2 Ha Hx Hs. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod F 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M8.
unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* a register of the last state that holds the start value of register r' *)
Lemma e01pb_reg_of : forall E ss ms (H : word -> bool) regs extra (r r' : bv 5),
  st_ok rsegs E ss (restrict H ms) -> E = Ereg regs extra ->
  sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r')) 0) = true ->
  getr (ms_regs ms) r = getr regs r'.
Proof.
intros E ss ms H regs extra r r' HS -> Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hq.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_reg.
Qed.

(* a register of the last state that holds the j-th extra atom *)
Lemma e01pb_reg_ext : forall E ss ms (H : word -> bool) regs extra (r : bv 5) (j : nat),
  st_ok rsegs E ss (restrict H ms) -> E = Ereg regs extra ->
  sv_eqb (sr_get (ss_regs ss) r) (SOff (32 + j) 0) = true ->
  getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros E ss ms H regs extra r j HS -> Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg rsegs H _ ss ms r HS), Hq.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_extra.
Qed.

(* the bytes a region's literal chunks show (role RPgW3a.v w3_lit_at, for every byte of pat at once) *)
Lemma e01pb_bytes_of_chk : forall E H mem (k : nat) b lo hi wlo whi cs pat,
  region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs) -> bv_unsigned (ew E k) = b ->
  e01pb_chk cs pat = true ->
  forall i, 0 <= i < Z.of_nat (length pat) -> aview rsegs H mem (b + i) = Some (nth (Z.to_nat i) pat 0).
Proof.
intros E H mem k b lo hi wlo whi cs pat (_ & _ & _ & Hcs) Hb Hchk i Hi.
unfold e01pb_chk in Hchk. rewrite forallb_forall in Hchk.
assert (Hin : In (Z.to_nat i) (seq 0 (length pat))) by (apply in_seq; lia).
specialize (Hchk _ Hin). unfold e01pb_chk1 in Hchk. apply existsb_exists in Hchk as (c & Hc & Hm).
destruct c as [o cv]. destruct cv as [w v | l | l | d s l]; try discriminate Hm.
destruct v as [z | | | | | | | | | |]; try discriminate Hm.
apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [H1 H2].
apply Z.eqb_eq in H1. apply N.eqb_eq in H2. apply Z.eqb_eq in H3. subst o w.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hm1). cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hm1.
rewrite Z.add_0_r, Z2Nat.id in Hm1 by lia. injection Hb1 as <-. unfold aview. rewrite Hm1. cbn [option_map]. f_equal.
rewrite <- H3. unfold byte_of_word. cbn [sv_denot]. rewrite Z.shiftr_0_r, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.

(* every byte outside a run's write windows is kept (role RPgW3a.v w3_keep_run) *)
Lemma e01pb_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
  frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.

End h.

Ltac e01pb_reg HS HE r' := erewrite (e01pb_reg_of _ _ _ _ _ _ _ r' HS HE) by (vm_compute; reflexivity).

(* ======================================== the part ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : 0x230 + ASTACK <= LLVMF_STK.

Theorem e01b_pro_ok : e01b_pro_stmt B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros hx POST HB HK pos lyc Sc W regs mem md HFR.
unfold e01b_from_hd in HK.
destruct hx as [ly0 St0 W0 regs0 mem0 md0 p n pl].
unfold rhb_base in HB. unfold e01b_fr, e01b_base, rhb_j, rhb_kept, e01b_env, e01b_R, e01b_S, e01b_F in HFR.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl] in HB, HFR.
destruct HB as (HPRE & _ & _ & _ & Hpn & Hlen & _ & _ & _ & _ & _).
destruct HFR as ((HJ & Hfrs & Habl & HKEPT & HIN) & G2 & G3 & G4 & G8 & G9 & G18 & G20 & G21 & G10).
pose proof (YG0q.AR_laws_ok rsegs B) as HL. pose proof rtsb_segs_low as Hsegs. pose proof rtsb_wx as Hwx.
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
unfold RSB_RSZ, RSB_CID in *.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
clear HPRE Hstk0.
set (S0 := spZ regs0) in *.
set (R := 32 * ((S0 - 544) / 32)) in *.
set (F := frame_addr ly0 4 pos) in *.
assert (HS0 : alloc_ceiling + LLVMF_STK <= S0 <= 2 ^ 47) by lia.
clear Hceil Hslo Hshi H47.
(* R = S - 0x220 or S - 0x230 (S is 16-aligned) *)
assert (HR : R mod 32 = 0 /\ S0 - 0x230 <= R <= S0 - 0x220).
{ unfold R. pose proof (Z.div_mod (S0 - 544) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (S0 - 544) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod S0 16 ltac:(lia)) as D16. rewrite Hal16, Z.add_0_r in D16.
  split; [rewrite Z.mul_comm; apply Z_mod_mult | lia]. }
clear Hal16.
(* ---- the frame for locals at the state FR ---- *)
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
assert (EFA : frame_addr lyc 4 pos = F).
{ destruct Hly as (_ & _ & _ & _ & _ & EFl & _). unfold F, frame_addr. rewrite EFl. reflexivity. }
clear Hly.
destruct (al_frames _ _ HL _ _ _ _ _ 4 pos HAR Hin4) as (HFal & HFapp & HFpres & HFSpres).
destruct (frames_bounds rsegs B HL _ _ _ _ _ 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite EFA in HFal, HFapp, HFpres, HFSpres, HF4096, HFceil.
change (fs_frame_bytes 4) with 1024 in HFapp, HFpres, HFSpres, HFceil.
change (1024 / 8) with 128 in HFSpres.
pose proof (rtsb_fbounds F HFal HFapp) as (_ & _ & Hsh0 & HshC & HFsh & _).
set (shF := shadow_addr F) in *.
assert (Hn26 : 0 <= n < 2 ^ 26) by (destruct Hpn as [(-> & _) | (Hn & _)]; lia).
(* ---- the engine's environment ---- *)
remember (Ereg regs [Z_to_bv 64 shF]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 R) by (subst E; rewrite (ew_Ereg_nat regs _ 9 (9%bv : bv 5) eq_refl), G9; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (subst E; rewrite (ew_Ereg_nat regs _ 10 (10%bv : bv 5) eq_refl), G10; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite (ew_Ereg_nat regs _ 20 (20%bv : bv 5) eq_refl), G20; reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 n) by (subst E; rewrite (ew_Ereg_nat regs _ 21 (21%bv : bv 5) eq_refl), G21; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 shF) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = shF) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E e01pb_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 E01B_FR) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. rewrite HE. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - rewrite <- HE. unfold E01PB_R, E01PB_F, E01PB_SH.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply HJpres. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply HFpres. lia.
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply HFSpres. lia.
  - rewrite <- HE. apply pairwise_disjoint_of_extents. unfold E01PB_R, E01PB_F, E01PB_SH, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U10, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - HR HS0 HSTK Has HFceil HshC HFsh. repeat split; lia.
  - rewrite <- HE. unfold facts_ok, e01pb_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U10, E21, (unsigned_lit_small n) by lia.
      change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
      clear - HR HS0 HSTK Has C1 HFal HF4096 HFceil Hn26. repeat split; lia.
    + split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_eq_U, (e01pb_srl26 E 21 n E21 Hn26), U_SLit. reflexivity.
    + split; [|exact I]. exact (shadow_decl_ok E 10 20 32 F SHADOW_OFF E10 ltac:(lia) E20 E32). }
(* ---- the run 0x807e0 .. 0x809bc ---- *)
unfold cfg_at. change (w64 E01B_FR) with (Z_to_bv 64 E01B_FR).
aj_run_to e01pb_tbl_ok HS HJ E01B_HD.
{ unfold e01pb_ss, E01PB_R, E01PB_F, E01PB_SH. cbn [ss_mem].
  apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - S0));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (rtsb_awr_ok_fobj E _ _ _ _ _ _ _ _ _ 10%nat pos 0);
    [reflexivity | rewrite U10, EFA; lia | left; reflexivity | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply (rtsb_awr_ok_fsh E _ _ _ _ _ _ _ _ _ 32%nat pos);
    [reflexivity | rewrite U32, EFA; reflexivity | left; reflexivity | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_nil. }
lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msF end.
(* every byte outside the three windows is kept *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (R + 0x190 <= a < R + 0x198) -> ~ (F <= a < F + 24) ->
  ~ (shF <= a < shF + 88) -> aview rsegs (w_H W) (ms_mem msF) a = aview rsegs (w_H W) mem a).
{ intros a Ha N1 N2 N3.
  apply (e01pb_keep_run E (ss_mem e01pb_ss) (w_H W) mem (ms_mem msF)
    (fun x => (R + 0x190 <= x < R + 0x198) \/ (F <= x < F + 24) \/ (shF <= x < shF + 88)) HFr); [| exact Ha | tauto].
  intros x (r & Hr & Hb). unfold e01pb_ss, E01PB_R, E01PB_F, E01PB_SH in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    rewrite ?U9, ?U10, ?U32 in Hb; lia. }
(* the frame's shadow, from the last state's shadow region *)
assert (FSH : rt_fsh rsegs (w_H W) (ms_mem msF) F rsb_P0).
{ lazymatch type of HS with st_ok _ _ ?ssf _ =>
    let r2 := eval vm_compute in (nth_error (ss_mem ssf) 2) in
    lazymatch r2 with Some ?rr =>
      pose proof (rtsb_region_nth E ssf msF 2 rr (w_H W) HS ltac:(vm_compute; reflexivity)) as HR2 end end.
  intros i Hi. exact (e01pb_bytes_of_chk E (w_H W) (ms_mem msF) 32 shF _ _ _ _ _ rsb_P0 HR2 U32
    ltac:(vm_compute; reflexivity) i Hi). }
(* ---- the state HD ---- *)
rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msF HS eq_refl) at 1. cbn [ss_pc].
apply (HK pos lyc Sc W (ms_regs msF) (ms_mem msF)).
unfold e01b_hd, e01b_base, rhb_j, rhb_kept, e01b_env, e01b_R, e01b_S, e01b_F, RSB_CID, RSB_RSZ.
cbn [h_ly h_S h_W h_regs h_mem h_md h_p h_n h_pl].
change (spZ regs0) with S0. change (32 * ((S0 - 544) / 32)) with R. change (frame_addr ly0 4 pos) with F.
split.
{ split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Habl|]. split.
  - (* the 13 saves and the flag pointer word *)
    unfold rhb_cells in HKEPT |- *. rewrite Forall_forall in HKEPT |- *. intros f Hf.
    pose proof (HKEPT f Hf) as Hf'.
    apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
    + unfold rhb_saves_L in Hf. apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj.
      cbn [fst snd rt_at rt_xv q_S] in Hf' |- *.
      apply (rtsb_val_kept (w_H W) mem (ms_mem msF) _ 8 _); [|exact Hf'].
      intros k Hk. apply KEEP; clear - Hj Hk HR HS0 HSTK Has C1 HFceil HshC; lia.
    + cbn [fst snd rt_at rt_xv q_F] in Hf' |- *.
      apply (rtsb_val_kept (w_H W) mem (ms_mem msF) _ 8 _); [|exact Hf'].
      intros k Hk. apply KEEP; clear - Hk HR HS0 HSTK Has C1 HF4096 HFceil HFsh; lia.
  - (* the input bytes *)
    apply (rtmb_bytes_kept rsegs (w_H W) mem (w_H W) (ms_mem msF) p pl HIN).
    intros x Hx. rewrite <- Hlen in Hx.
    destruct Hpn as [(Hn0 & _) | (Hn & Hinb)]; [lia|].
    rewrite <- Habl in Hinb.
    destruct (al_blocks _ _ HL _ _ _ _ _ _ _ HAR Hinb) as (_ & Hp4096 & Hpceil & Hpapp & _).
    pose proof (sep_block_frame rsegs B HL _ _ _ _ _ _ _ 4 pos HAR Hinb Hin4) as Hdisj.
    rewrite EFA in Hdisj. unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. change (fs_frame_bytes 4) with 1024 in Hdisj.
    assert (Hrq : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
    rewrite Hrq in Hpceil, Hpapp, Hdisj.
    apply KEEP.
    + clear - Hx Hp4096 Hpceil C1. lia.
    + clear - Hx Hpceil HR HS0 HSTK Has. lia.
    + clear - Hx Hdisj. lia.
    + intros Hs. apply (e01pb_sh_not_app F p n x HF4096 HFceil Hpapp Hx). fold shF. lia. }
(* ---- the registers ---- *)
split; [e01pb_reg HS HE (2%bv : bv 5); exact G2|].
split; [e01pb_reg HS HE (3%bv : bv 5); exact G3|].
split; [e01pb_reg HS HE (4%bv : bv 5); exact G4|].
split; [e01pb_reg HS HE (8%bv : bv 5); exact G8|].
split; [e01pb_reg HS HE (9%bv : bv 5); exact G9|].
split; [e01pb_reg HS HE (18%bv : bv 5); exact G18|].
split; [erewrite (e01pb_reg_ext _ _ _ _ _ _ _ 0%nat HS HE) by (vm_compute; reflexivity); reflexivity|].
split; [e01pb_reg HS HE (20%bv : bv 5); exact G20|].
split; [e01pb_reg HS HE (21%bv : bv 5); exact G21|].
split; [e01pb_reg HS HE (10%bv : bv 5); exact G10|].
split; [e01pb_reg HS HE (10%bv : bv 5); exact G10|].
exact FSH.
Qed.

End b.

Print Assumptions e01b_pro_ok.
