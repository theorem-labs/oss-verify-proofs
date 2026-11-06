(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite this unit's own image (YImgTop.IMG_LO and YImgTop.IMG_TOP, which YImgTop.v of reac-pw/fuzz_rate gives as 0x10000 and 0x5fa000, both of this unit's ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Reusable/YCbq.v, with its module paths and module names changed; 442 of its 486 lines of code are new or changed and 3116 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_k3.v, with its module names changed; 123 of its 173 lines of code are new or changed and 436 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel's attribute cases after the texts load (kernel_defs.v kin_txt,
   +0xa74) and the empty cursor's attribute (kin_acase KP_A0 ka_empty, +0xb10): the symbolic state at +0xa74, the
   attribute byte's case a % 6 as the engine's branch conditions, and the cut facts the case files share.
   Listing (internal path) (internal record, sha256 7bc02d6772b3), +0xa74 .. +0xb44:
     +0xa74  a0 := slot 0xb8 (0x2aaaaaaaaaaaaaab); a1 := s7 - 6 * mulhu(s7, a0) = a % 6 (tx_A1)
     +0xa90  `bge 1, a1` -> +0xad8: `beqz a1` -> +0xb10 (a % 6 = 0); `bne a1, 1` -> +0xc24 is not taken (a % 6 = 1):
             checked_memset(long_alias, 0x61, 300) at +0xaf8, then attr_text(w2, 20, long_alias, 0) at +0xb40
     +0xa94  a0 := a1 - 2 (tx_A2); `bgeu a0, 2` -> +0xb24; not taken: +0xaa0 = KP_A23 (a % 6 in {2, 3})
     +0xb24  `bne a1, 4` -> +0xc24 = KP_A5 (a % 6 = 5); a % 6 = 4: attr_text(w2, 3, .str.8, 0) at +0xb40
     +0xb10  a3 := a & 0x80; attr_text(w2, 20, s11 = p, a3) at +0xb40 (a % 6 = 0, and the empty cursor)
   THE STATE at +0xa74: registers `sr_atoms` (s7 = atom 23 = a), one region at s1 (atom 9) holding the slots 0xb0
   (a0 + 8) and 0xb8 (the magic), nothing written; facts s1, s4 and a in [0, 255]; the case's branch conditions
   (tx_c0 .. tx_c5) over tx_A1 / tx_A2, true by `tx_val` (the 256 values of a).
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
attr_text_c LinkWalkCall kernel_entry kernel_next kernel_ocall kernel_msg0_kit kernel_atcall.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0xa74 ---- *)
Definition tx_A1 : sv := SAlu ALU_ADD (SOff 23 0)
  (SAlu ALU_SUB (SAlu ALU_SLL (SMd M_MULHU (SOff 23 0) (SLit KI_M6_V)) (SLit 1))
                (SAlu ALU_SLL (SMd M_MULHU (SOff 23 0) (SLit KI_M6_V)) (SLit 3))).
Definition tx_A2 : sv := SAlu ALU_ADD tx_A1 (SLit (-2)).
Definition tx_c0 : list acond := [mkAC BC_GE (SLit 1) tx_A1; mkAC BC_EQ tx_A1 (SLit 0)].
Definition tx_c1 : list acond :=
  [mkAC BC_GE (SLit 1) tx_A1; mkAC BC_NE tx_A1 (SLit 0); mkAC BC_EQ tx_A1 (SLit 1)].
Definition tx_c23 : list acond := [mkAC BC_LT (SLit 1) tx_A1; mkAC BC_LTU tx_A2 (SLit 2)].
Definition tx_c4 : list acond :=
  [mkAC BC_LT (SLit 1) tx_A1; mkAC BC_GEU tx_A2 (SLit 2); mkAC BC_EQ tx_A1 (SLit 4)].
Definition tx_c5 : list acond :=
  [mkAC BC_LT (SLit 1) tx_A1; mkAC BC_GEU tx_A2 (SLit 2); mkAC BC_NE tx_A1 (SLit 4)].
Definition tx_cs (m : Z) : list acond :=
  if m =? 0 then tx_c0 else if m =? 1 then tx_c1 else if (m =? 2) || (m =? 3) then tx_c23
  else if m =? 4 then tx_c4 else tx_c5.
Definition tx_rg : YP09.region := YP09.mkRegion (Some 9%nat) 0xb0 0xc0 0xb0 0xb0
  [YP09.mkChunk 0xb0 (CVal 8 (SOff 18 8)); YP09.mkChunk 0xb8 (CVal 8 (SLit KI_M6_V))].
Definition tx_atoms : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (23%nat, mkAF 0 255 0)].
Definition tx_ss (cs : list acond) : sstate := mkSS (kpc KP_TXT) sr_atoms [tx_rg] None (mkFacts tx_atoms cs []).
(* the empty cursor's attribute at +0xb10: no region, no condition *)
Definition tx_ss0 : sstate := mkSS (kpc KP_A0) sr_atoms [] None (mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition tx_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition tx_Bx : sv := SOff 20 0.
(* the registers no case writes before its cut or call: s3, s5, s6, s7, s8, s9, s11 *)
Definition tx_keep : list nat := [19; 21; 22; 23; 24; 25; 27]%nat.

(* a1 = a % 6 and a1 - 2, for each of the 256 values of a *)
Lemma tx_val : forall (E : env) a, ew E 23%nat = Z_to_bv 64 a -> 0 <= a < 256 ->
  sv_denot E tx_A1 = Z_to_bv 64 (a mod 6) /\ sv_denot E tx_A2 = Z_to_bv 64 (a mod 6 - 2).
Proof.
  intros E a Ha Hr. unfold tx_A2, tx_A1, KI_M6_V. cbn [sv_denot]. rewrite !Ha.
  assert (Hin : In a (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat a). split; [apply Z2Nat.id; lia | apply in_seq; lia]. }
  clear Hr. cbn [seq map] in Hin.
  repeat (destruct Hin as [<- | Hin]; [split; apply bv_eq; vm_compute; reflexivity |]). destruct Hin.
Qed.

Lemma tx_conds : forall (E : env) a, ew E 23%nat = Z_to_bv 64 a -> 0 <= a < 256 ->
  conds_ok E (tx_cs (a mod 6)).
Proof.
  intros E a Ha Hr. destruct (tx_val E a Ha Hr) as (D1 & D2).
  pose proof (Z.mod_pos_bound a 6 ltac:(lia)) as Hm.
  assert (Hc : a mod 6 = 0 \/ a mod 6 = 1 \/ a mod 6 = 2 \/ a mod 6 = 3 \/ a mod 6 = 4 \/ a mod 6 = 5) by lia.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]; rewrite Hc in D1, D2 |- *;
    [change (tx_cs 0) with tx_c0; unfold tx_c0 | change (tx_cs 1) with tx_c1; unfold tx_c1
    | change (tx_cs 2) with tx_c23; unfold tx_c23 | change (tx_cs 3) with tx_c23; unfold tx_c23
    | change (tx_cs 4) with tx_c4; unfold tx_c4 | change (tx_cs 5) with tx_c5; unfold tx_c5];
    cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?D1, ?D2;
    change (sv_denot E (SLit 0)) with (Z_to_bv 64 0); change (sv_denot E (SLit 1)) with (Z_to_bv 64 1);
    change (sv_denot E (SLit 2)) with (Z_to_bv 64 2); change (sv_denot E (SLit 4)) with (Z_to_bv 64 4);
    repeat split; vm_compute; reflexivity.
Qed.

(* the cut's register list as values *)
Lemma tx_getr : forall (ms : machine_state) rl (r : nat) (b : bv 5) v,
  kregs_eq ms rl -> In (r, v) rl -> Z.of_nat r = bv_unsigned b -> getr (ms_regs ms) b = w64 v.
Proof.
  intros ms rl r b v H Hin Hb.
  replace b with (Z_to_bv 5 (Z.of_nat r)).
  - exact (kn_reg_in ms rl r v H Hin).
  - apply bv_eq. rewrite Z_to_bv_unsigned, Hb. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* the cut kms at a callee's entry, from the plain engine's state at the call *)
Lemma tx_kms_of : forall (H : word -> bool) E ss (ms : machine_state) (pc : Z),
  st_ok SEGS E ss (restrict H ms) -> ss_resv ss = None -> ss_pc ss = BASE + kpc pc -> kms pc ms.
Proof.
  intros H E ss ms pc HS Hrv Hpc.
  pose proof (st_ok_restrict_mkst SEGS H E ss ms HS Hrv) as Hsh. rewrite Hpc in Hsh.
  unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  do 5 (split; [reflexivity|]). reflexivity.
Qed.

Lemma tx_sigma_atext : pa_sigma LS_attr_text = BASE + kpc KP_ATEXT.
Proof. rewrite pa_sigma_attr_text. unfold kpc, AF_kernel, KP_ATEXT, AF_attr_text. lia. Qed.

(* the attribute case's case: kin_txt with the case of a % 6 *)
Definition kin_txtc (Rc Rm Ra : kcx -> Z -> Prop) (P : Z -> Prop)
  : kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists a p, 0 <= a < 256 /\ P (a mod 6) /\ au64_at SEGS (km0 cx) (LA_TEXTS + 8 * ((a / 8) mod 11)) p /\
  ktext cx p /\ kattr B Rc Rm Ra KP_TXT [(23%nat, a); (27%nat, p)] (fun _ _ => True) cx fpos k2 ly3 S3 W3 ms3 md3.

(* the state at +0xa74 for a branch condition list cs that holds *)
Lemma tx_seat : forall cx fpos k2 ly3 S3 md3 W3 ms3 sl a cs,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kms KP_TXT ms3 -> kregs0 cx ms3 -> kslots_eq cx W3 ms3 sl ->
  In (KS_CN, ka0 cx + 8) sl -> In (KS_M6, KI_M6_V) sl ->
  getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 23)) = w64 a -> 0 <= a < 256 ->
  conds_ok (Eimg (Ereg (ms_regs ms3) [])) cs ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (tx_ss cs) (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 md3 W3 ms3 sl a cs HB HJB HMS HR0 HSL Hcn Hm6 R23 Ha Hcs.
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof (kn_sp1 SK B cx HB) as (S1a & S1b & S1c & _ & _ & S1f & _).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx + 15) HB HJB (kn_ard_cur cx (ka0 cx + 15) ltac:(lia)))
    as (CL & _).
  destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 (ka0 cx) HB HJB (kn_ard_cur cx (ka0 cx) ltac:(lia)))
    as (CL0 & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (ER : forall (jn : nat) (r : bv 5), Z.of_nat jn = bv_unsigned r -> ew E jn = getr (ms_regs ms3) r)
    by (intros jn r Hjr; exact (ew_Eimg_Ereg_nat _ _ jn r Hjr)).
  assert (E18 : ew E 18%nat = w64 (ka0 cx)) by (rewrite (ER 18%nat 18%bv eq_refl); exact A18).
  assert (E9 : ew E 9%nat = w64 (ksp1 cx)) by (rewrite (ER 9%nat 9%bv eq_refl); exact A9).
  assert (E20 : ew E 20%nat = w64 SHADOW_OFF) by (rewrite (ER 20%nat 20%bv eq_refl); exact A20).
  assert (E23 : ew E 23%nat = w64 a) by (rewrite (ER 23%nat (Z_to_bv 5 (Z.of_nat 23)) eq_refl); exact R23).
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  pose proof (kn_slot_of cx W3 ms3 sl KS_CN (ka0 cx + 8) HSL Hcn) as SL_CN.
  pose proof (kn_slot_of cx W3 ms3 sl KS_M6 KI_M6_V HSL Hm6) as SL_M6.
  rewrite (kn_ms_shape ms3 (BASE + kpc KP_TXT) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  unfold tx_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold tx_rg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8)); [|exact SL_CN].
      cbn [sv_denot]. rewrite BV18. reflexivity.
    + exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb8 (SLit KI_M6_V) KI_M6_V eq_refl SL_M6).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [|split; [exact Hcs | exact I]].
    unfold tx_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E20, E23. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; first [lia | exact I | exact S1b].
Qed.

(* kernel_apre's .str.8 and long_alias facts *)
Lemma tx_apre_x : forall cx, kbase SK B cx ->
  kernel_str SEGS (k_regs cx) (km0 cx) LA_STR_X /\
  (exists la sl, au8arr SEGS (km0 cx) LA_LONG_ALIAS (la ++ [zb 0]) /\ Z.of_nat (length la) = 300
     /\ abytes SEGS (km0 cx) (LA_LONG_ALIAS + LONG_ALIAS_SIZE) sl /\ length sl = 3%nat) /\
  range_addressable (ard SEGS (km0 cx)) SHADOW_OFF LA_LONG_ALIAS LONG_ALIAS_SIZE /\
  shadow_hull_vis (ard SEGS (km0 cx)) LA_LONG_ALIAS LONG_ALIAS_SIZE /\
  apart_frame (k_regs cx) KERNEL_AK LA_LONG_ALIAS (LONG_ALIAS_SIZE + 3).
Proof.
  intros cx HB. pose proof HB as (_ & _ & HKP & _).
  destruct HKP as (kbs' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    HSX & HLA & HRALA & HHVLA & HAFLA & _).
  tauto.
Qed.

End b.
End a.

Print Assumptions tx_seat.
