(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 359 of its 392 lines of code are new or changed and 36 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntHdrLib DiscoEntHdrCut.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition mid_sr : list sv :=
  [SLit 0; SOff 537 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 538 0; SOff 534 0; SOff 532 0;
   SOff 2 0; SOff 60 0; SMd M_MUL (SOff 536 0) (SLit 1000000); SOff 533 0; SOff 539 0; SOff 540 0; SOff 516 2160; SOff 541 0;
   SOff 531 0; SExt true 8 (SOff 535 0); SOff 32 0; SOff 542 0; SLit WS_MASK; SOff 543 0; SOff 516 2992; SOff 544 0;
   SOff 545 0; SLit 32; SOff 516 2128; SOff 546 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 550 0].
Definition mid_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 232 352 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_loop)].
Definition mid_ss : sstate := mkSS MID_OFF mid_sr mid_rs None (d_facts [] []).

Lemma h2_w64_sext : forall b, 0 <= b < 256 ->
  Z_to_bv 64 (if b <? 128 then b else b + (2 ^ 64 - 256)) = w64 (if b <? 128 then b else b - 256).
Proof.
intros b Hb. unfold w64. destruct (b <? 128); [reflexivity|]. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
replace (b - 256) with ((b + (2 ^ 64 - 256)) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma h2_now_range : forall op dt now, 0 <= now < 2 ^ 64 -> 0 <= dt < 65536 -> 0 <= hdr_now op dt now < 2 ^ 64.
Proof.
intros op dt now Hn Hd. unfold hdr_now. destruct (op <? 128).
- apply Z.mod_pos_bound. lia.
- destruct (Z.ltb_spec now (dt * 1000000)); lia.
Qed.

Section u.
Variable E : env.
Lemma h2_blt_op : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  branch_taken BC_LT (sv_denot E (SExt true 8 (SOff k 0))) (sv_denot E (SLit 0)) = (128 <=? b).
Proof.
intros k b Hk Hb. rewrite hd_br_lt, (hd_S_sext8 E k b Hk Hb), hd_S_lit0.
destruct (Z.ltb_spec b 128).
- rewrite (proj2 (Z.ltb_ge b 0)) by lia. symmetry. apply Z.leb_gt. lia.
- rewrite (proj2 (Z.ltb_lt (b - 256) 0)) by lia. symmetry. apply Z.leb_le. lia.
Qed.
Lemma h2_bne_op3 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SExt true 8 (SOff k 0)) (SLit 3))) (sv_denot E (SLit 3)) = negb (b mod 4 =? 3).
Proof. intros k b Hk Hb. rewrite branch_ne_U, (hd_U_op3 E k b Hk Hb), U_lit by lia. reflexivity. Qed.
Lemma h2_U_mul : forall k dt, ew E k = Z_to_bv 64 dt -> 0 <= dt < 65536 ->
  sv_denot E (SMd M_MUL (SOff k 0) (SLit 1000000)) = w64 (dt * 1000000).
Proof.
intros k dt Hk Hd. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E k dt Hk) by lia. rewrite U_SLit. change (zcanon 1000000) with 1000000.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma h2_U_nowsub : forall X dt k now, U E X = dt -> 0 <= dt < 65536 -> ew E k = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLTU (SOff k 0) (SAlu ALU_ADD (SOff k 0) (SMd M_MUL X (SLit (-1000000)))))
                     (SLit (-1))) (SAlu ALU_ADD (SOff k 0) (SMd M_MUL X (SLit (-1000000)))))
  = if now <? dt * 1000000 then 0 else now - dt * 1000000.
Proof.
intros X dt k now HX Rdt Hk Rn.
assert (US : U E (SAlu ALU_ADD (SOff k 0) (SMd M_MUL X (SLit (-1000000)))) =
  if now <? dt * 1000000 then now - dt * 1000000 + 2 ^ 64 else now - dt * 1000000).
{ rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite HX, U_SLit, (U_atom E k now Hk) by lia.
  change (zcanon (-1000000)) with (2 ^ 64 - 1000000). unfold zcanon, M64.
  rewrite Zplus_mod_idemp_r.
  replace (now + dt * (2 ^ 64 - 1000000)) with ((now - dt * 1000000) + dt * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia.
  destruct (Z.ltb_spec now (dt * 1000000)).
  - rewrite <- (Z.mod_add (now - dt * 1000000) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.mod_small. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite US. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite US, (U_atom E k now Hk), U_SLit by lia. change (zcanon (-1)) with (2 ^ 64 - 1).
destruct (Z.ltb_spec now (dt * 1000000)).
- rewrite (proj2 (Z.ltb_lt now (now - dt * 1000000 + 2 ^ 64))) by lia.
  replace (zcanon (zcanon 1 + (2 ^ 64 - 1))) with 0 by reflexivity. rewrite Z.land_0_l. reflexivity.
- rewrite (proj2 (Z.ltb_ge now (now - dt * 1000000))) by lia.
  replace (zcanon (zcanon 0 + (2 ^ 64 - 1))) with (2 ^ 64 - 1) by reflexivity. rewrite (hd_land_m1 (now - dt * 1000000)) by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma h2_U_nowadd : forall X dt k now, U E X = dt -> 0 <= dt < 65536 -> ew E k = Z_to_bv 64 now -> 0 <= now < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff k 0) (SMd M_MUL X (SLit 1000000))) = (dt * 1000000 + now) mod 2 ^ 64.
Proof.
intros X dt k now HX Rdt Hk Rn. rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw]. rewrite HX, U_SLit, (U_atom E k now Hk) by lia.
change (zcanon 1000000) with 1000000. rewrite (zcanon_id (dt * 1000000)) by (unfold M64; lia).
unfold zcanon, M64. f_equal. lia.
Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition mid_vals (cx : dcx) (i n now op dt : Z) (regs : bvmap 5 word) : list word :=
  [w64 (d_cur cx n); w64 n; w64 now; w64 i; w64 op; w64 dt; getr regs 1; getr regs 5; getr regs 12; getr regs 13;
   getr regs 15; getr regs 19; getr regs 21; getr regs 23; getr regs 24; getr regs 27; getr regs 28; getr regs 29;
   getr regs 30; getr regs 31].
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma mid_geo : forall cx ly3 S3 (W3 : world SEGS) mem3 md3 k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_S cx - 608 < d_A cx <= d_S cx - 576 /\ 608 <= d_S cx <= 2 ^ 47 /\ 4096 <= d_FB cx /\ d_FB cx + 4096 < 2 ^ 64.
Proof.
intros cx ly3 S3 W3 mem3 md3 k (HB & HJ & HFR).
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & HLY & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY) as (_ & EFA3 & _).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF0 & HFc & _).
rewrite EFA3 in HF0, HFc. fold (d_FB cx) in HF0, HFc.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in HFc.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (hd_A_range cx HS608) as [HAr _].
split; [exact HAr|]. split; [split; [exact HS608 | unfold d_S, LLVMF_STK in *; lia]|].
split; [exact HF0 | lia].
Qed.

Lemma mid_seat : forall (fq : YK11.FPState) (cx : dcx) (i n now op dt : Z) ly3 S3 (W3 : world SEGS) (regs : bvmap 5 word) mem3 md3 k
  (E : env),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx dsh_loop) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_rM B cx i n now op dt regs -> 0 <= op < 256 -> 0 <= dt < 65536 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (mid_vals cx i n now op dt regs)) mid_ss
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + MID_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx i n now op dt ly3 S3 W3 regs mem3 md3 k E HC HE HRG HFL HR Rop Rdt.
set (vals := mid_vals cx i n now op dt regs).
destruct (mid_geo cx ly3 S3 W3 mem3 md3 k HC) as (_ & _ & HF0 & HF1).
pose proof HC as (HB & _ & _).
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HE as (EE & E32 & _ & E60 & E516 & _). unfold AT_A, AT_F in E60, E516.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) & H6 & H7 & H10 & H11 & H14 & H16 & H17 & H22 & H26).
assert (EL : forall q, (q < 530)%nat -> ew (d_env cx E vals) q = ew E q) by (intros q Hq; unfold d_env; apply ew_havoc_old; exact Hq).
assert (EV : forall q j, q = (531 + j)%nat -> (j < 20)%nat -> ew (d_env cx E vals) q = nth j vals (Z_to_bv 64 0)).
{ intros q j -> Hj. unfold d_env. replace (531 + j)%nat with (AT_FL + S j)%nat by (unfold AT_FL; lia).
  rewrite (ew_havoc_new E AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; unfold vals, mid_vals; cbn [length]; lia). reflexivity. }
assert (UFB : bv_unsigned (ew E 516) = d_FB cx) by (rewrite E516; apply unsigned_lit_small; lia).
assert (E2 : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ly3 S3 W3 regs mem3 md3 k E MID_OFF mid_sr vals [] [] []
  (d_facts [] []) HC HE HRG HFL) as HSEAT.
assert (HREGS : regs_ok (d_env cx E vals) mid_sr regs).
{ apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [ <- | Hr ];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H20 | exact H25 ]
      | |- _ = sv_denot _ (SOff 516 _) => cbn [sv_denot]; rewrite EL by lia; rewrite UFB;
          first [ rewrite H14 | rewrite H22 | rewrite H26 ]; unfold w64, d_obj, dobj_off; reflexivity
      | |- _ = sv_denot ?Ex (SMd M_MUL (SOff 536 0) (SLit 1000000)) =>
          rewrite H10; symmetry; apply (h2_U_mul Ex 536 dt); [rewrite (EV 536%nat 5%nat eq_refl ltac:(lia)); reflexivity | exact Rdt]
      | |- _ = sv_denot ?Ex (SExt true 8 (SOff 535 0)) =>
          rewrite H17, denot_lit_U, (hd_U_sext8 Ex 535 op); [symmetry; apply h2_w64_sext; exact Rop
          | rewrite (EV 535%nat 4%nat eq_refl ltac:(lia)); reflexivity | exact Rop]
      | |- _ = sv_denot _ (SOff ?q 0) => rewrite sv_denot_SOff0;
          lazymatch eval vm_compute in (Nat.ltb q 530) with
          | true => rewrite EL by lia;
              first [ rewrite E60; first [ exact H9 | unfold w64; rewrite <- Hsp; unfold YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned ]
                    | rewrite E32; exact H18
                    | rewrite E2; exact H8
                    | rewrite (EE 3%nat 3%bv eq_refl), Hgp0; exact Hgp
                    | rewrite (EE 4%nat 4%bv eq_refl), Htp0; exact Htp ]
          | false => let j := eval vm_compute in (q - 531)%nat in
              rewrite (EV q j eq_refl ltac:(lia)); unfold vals, mid_vals; cbn [nth];
              first [ reflexivity | assumption ]
          end
      end
    | ]).
  destruct Hr. }
assert (HFACTS : facts_ok (d_env cx E vals) (d_facts [] []))
  by exact (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k E vals [] [] HC HE I I).
assert (HSUB : submem mid_rs (d_kregions dsh_loop [] [] ++ [])).
{ unfold mid_rs, d_kregions. cbn [app].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_nil. }
specialize (HSEAT HREGS HFACTS (Forall_nil _) (Forall_nil _) (Forall_nil _) ltac:(cbn; tauto) (Forall_nil _)
  ltac:(vm_compute; reflexivity)).
exact (st_ok_pi_submem _ _ _ mid_rs HSEAT HSUB ltac:(vm_compute; reflexivity)).
Qed.

Ltac hew := cbn [ew havoc d_env AT_FL Nat.ltb Nat.leb Nat.sub nth mid_vals].
Ltac hrewU := repeat match goal with
  | U : bv_unsigned (ew ?E0 ?q) = _ |- context [bv_unsigned (ew ?E0 ?q)] => rewrite U end.
Ltac hawr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros a (r & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [ <- | Hin ];
    [ cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi fshadow_region] in Ha;
      first [ exfalso; lia | left; revert Ha; hew; hrewU; intros Ha; unfold LLVMF_STK; lia ] | ]);
  destruct Hin.
Ltac hwin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | revert Ha; hew; hrewU; intros Ha; lia ] | ]);
  destruct Hin.
Ltac hupd :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2),
    MEQ : forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (hd_meq_frame Eo rs Hh m0 m1 m2 lo hi HFr ltac:(hwin) MEQ) as MEQ2; clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with
  | HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2), MPR : forall a, apresent _ ?m0 a -> apresent _ ?m1 a |- _ =>
    let MPR2 := fresh "MPR" in pose proof (hd_pres_grow Hh m0 m1 m2 HG MPR) as MPR2; clear MPR; rename MPR2 into MPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hrun RUNTO stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ (restrict (w_H _) _), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; [ hawr | hupd ]
  end.
Ltac henv Hc := lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ => Ex end.
Ltac hdE := lazymatch goal with HE : d_E ?cx ?E |- d_E ?cx ?Ec =>
  apply (hd_d_E_agree cx E Ec HE); let k0 := fresh "k0" in let Hk0 := fresh "Hk0" in intros k0 Hk0;
  repeat (rewrite ew_havoc_old by (unfold AT_FL in *; lia)); unfold d_env; apply ew_havoc_old; unfold AT_FL; lia end.
Ltac hsv op dt now :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => reflexivity
  | |- sv_denot _ (SOff 516 _) = _ => cbn [sv_denot]; hew; hrewU; unfold w64, d_obj, dobj_off; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ => rewrite sv_denot_SOff0; hew; first [ reflexivity | assumption ]
  | |- sv_denot ?Ex (SExt true 8 (SOff 535 0)) = _ =>
      rewrite denot_lit_U, (hd_U_sext8 Ex 535 op) by (first [ hew; reflexivity | lia ]); apply h2_w64_sext; lia
  | |- sv_denot ?Ex (SAlu ALU_AND (SExt true 8 (SOff 535 0)) (SLit 3)) = _ =>
      rewrite denot_lit_U, (hd_U_op3 Ex 535 op) by (first [ hew; reflexivity | lia ]); reflexivity
  | |- sv_denot ?Ex (SAlu ALU_AND (SExt true 8 (SOff 535 0)) (SLit 255)) = _ =>
      rewrite denot_lit_U, (hd_U_op255 Ex 535 op) by (first [ hew; reflexivity | lia ]); reflexivity
  | |- sv_denot ?Ex _ = _ =>
      rewrite denot_lit_U; first [ unfold w64 | idtac ]; f_equal; unfold hdr_now;
      first [ rewrite (proj2 (Z.ltb_ge op 128)) by lia | rewrite (proj2 (Z.ltb_lt op 128)) by lia ];
      first [ apply (h2_U_nowsub Ex (SOff 536 0) dt 533 now) | apply (h2_U_nowadd Ex (SOff 536 0) dt 533 now) ];
      first [ apply (U_atom Ex 536 dt); [hew; reflexivity | lia] | lia | hew; reflexivity ]
  end.
Ltac hreg op dt now :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms) |- _ =>
    lazymatch goal with
    | |- YG0d.spZ _ = _ =>
      unfold YG0d.spZ;
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms 2%bv HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) 2%bv) in change (sr_get (ss_regs ss) 2%bv) with e in R;
      rewrite R, sv_denot_SOff0; hew; first [ assumption | hrewU; reflexivity ]
    | |- getr _ ?r = _ =>
      let R := fresh "R" in pose proof (st_ok_pi_restrict_reg (w_H W) Ec ss ms r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
      rewrite R; clear R; hsv op dt now
    end
  end.
Ltac hfind off L :=
  lazymatch L with
  | YP09.mkChunk off (CVal _ ?e) :: _ => e
  | _ :: ?t => hfind off t
  end.
Ltac hval_at cx off op dt now :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss ?msr |- _ =>
    let L := eval vm_compute in (YP09.r_chunks (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 []))) in
    let e := hfind off L in
    let RA := fresh "RA" in
    pose proof (st_ok_pi_region_nth Ec ss msr 1 _ HS eq_refl) as RA; cbn [ms_mem restrict] in RA;
    apply (DiscoACjr.field_of_region Ec _ 60 (d_A cx) _ _ _ _ _ off 8 e _ RA);
    [ hew; first [ assumption | hrewU; reflexivity ] | clear; cbn [In]; repeat (first [ left; reflexivity | right ]) | hsv op dt now
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); first [ unfold MAX_OPS in *; lia | apply h2_now_range; lia ]
    | cbn; lia ]
  end.
Ltac hland cx h i n now op dt fq ly3 S3 W mem3 acc :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H _) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md ?k |- _ =>
    apply SRr_ret; unfold hdr_Q; exists n, (hdr_now op dt now), op;
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 2308 =>
      left; split; [ assumption |];
      unfold arm3_in; eapply hd_d_at_mono;
      [ apply (hdr_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h i n now ly3 S3 W mem3 md k acc Ec ss ms n
          (hdr_now op dt now) ARM3_OFF (d_rA3 B cx n (hdr_now op dt now) op)
          (0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= hdr_now op dt now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 = 3));
        [ assumption | assumption | exact HJ | assumption | assumption | assumption | assumption | assumption | hdE | hew; reflexivity
        | exact HS | reflexivity | reflexivity | vm_compute; reflexivity | assumption | assumption | assumption | lia
        | hval_at cx 232 op dt now | hval_at cx 344 op dt now
        | unfold d_rA3, d_rL; repeat split; hreg op dt now
        | split; [lia|]; split; [lia|]; split; [apply h2_now_range; lia|]; split; [lia | assumption] ]
      | let regs := fresh "regs" in let ly := fresh "ly" in let S := fresh "S" in let W' := fresh "W" in
        let mem := fresh "mem" in let md := fresh "md" in let Q := fresh "Q" in let P := fresh "P" in
        let SP := fresh "SP" in let BD := fresh "BD" in
        intros regs ly S W' mem md (Q & P & SP & BD); destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5);
        exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj P (conj SP BD))))))) ]
    | 2408 =>
      right; split; [ assumption |];
      unfold rec_in; eapply hd_d_at_mono;
      [ apply (hdr_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h i n now ly3 S3 W mem3 md k acc Ec ss ms n
          (hdr_now op dt now) REC_OFF (d_rD B cx i n (hdr_now op dt now) op)
          (0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= hdr_now op dt now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3));
        [ assumption | assumption | exact HJ | assumption | assumption | assumption | assumption | assumption | hdE | hew; reflexivity
        | exact HS | reflexivity | reflexivity | vm_compute; reflexivity | assumption | assumption | assumption | lia
        | hval_at cx 232 op dt now | hval_at cx 344 op dt now
        | unfold d_rD, d_rL; repeat split; hreg op dt now
        | split; [lia|]; split; [lia|]; split; [apply h2_now_range; lia|]; split; [lia | assumption] ]
      | let regs := fresh "regs" in let ly := fresh "ly" in let S := fresh "S" in let W' := fresh "W" in
        let mem := fresh "mem" in let md := fresh "md" in let Q := fresh "Q" in let P := fresh "P" in
        let SP := fresh "SP" in let BD := fresh "BD" in
        intros regs ly S W' mem md (Q & P & SP & BD); destruct Q as (Q1 & Q2 & Q3 & Q4 & Q5);
        exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj P (conj SP BD))))))) ]
    end
  end.
Ltac htail RUNTO RUN BR Hop cx h i n now op dt fq ly3 S3 W mem3 acc :=
  hrun RUNTO 2304;
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUN BR HS SHOK Bspan;
    [ lazymatch goal with Hc : branch_taken BC_NE _ _ = _ |- _ =>
        let Ex := henv Hc in rewrite (h2_bne_op3 Ex 535 op ltac:(hew; reflexivity) Hop) in Hc;
        apply negb_true_iff, Z.eqb_neq in Hc end;
      hrun RUNTO 2408; hland cx h i n now op dt fq ly3 S3 W mem3 acc
    | lazymatch goal with Hc : branch_taken BC_NE _ _ = _ |- _ =>
        let Ex := henv Hc in rewrite (h2_bne_op3 Ex 535 op ltac:(hew; reflexivity) Hop) in Hc;
        apply negb_false_iff, Z.eqb_eq in Hc end;
      hrun RUNTO 2308; hland cx h i n now op dt fq ly3 S3 W mem3 acc ]
  end.

Theorem hdr_s2 : hdr_seg2 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i W c (n & now & op & dt & HD).
destruct HD as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hdt & HR & HBD).
pose proof HBD as (T & G & Lk & H & HFRM & _).
pose proof HFRM as (E & HE & HRG & HFL & _ & _).
pose proof (mid_seat fq cx i n now op dt ly3 S3 W regs mem3 md3 k E (conj HB (conj HJ HFR)) HE HRG HFL HR Hop Hdt) as HS.
destruct (mid_geo cx ly3 S3 W mem3 md3 k (conj HB (conj HJ HFR))) as (HAr & HSr & HF0 & HF1).
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HE as (EE & E32 & HEI0 & E60 & E516 & _). unfold AT_A, AT_F in E60, E516.
assert (E2 : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (UA : bv_unsigned (ew E 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; lia).
assert (UF : bv_unsigned (ew E 516) = d_FB cx) by (rewrite E516; apply unsigned_lit_small; lia).
clear HPRE Hgp0 Htp0 EE T G Lk H HFRM HRG HFL.
unfold cfg_at; change (w64 (BASE + MID_OFF)) with (Z_to_bv 64 (BASE + MID_OFF)).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO; pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (HEI : img_env VAL A_LIM (d_env cx E (mid_vals cx i n now op dt regs))) by
  (apply img_env_havoc_hi; [exact HEI0 | unfold AT_FL, A_LIM; lia]).
pose proof (Forall_nil (shent_ok SEGS (SOff 32 0) (d_env cx E (mid_vals cx i n now op dt regs)) (mrestrict (w_H W) mem3)) :
  sh_ok SEGS (SOff 32 0) [] (d_env cx E (mid_vals cx i n now op dt regs)) (mrestrict (w_H W) mem3)) as SHOK.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 232 <= a < d_A cx + 352) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a)
  by reflexivity.
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by auto.
unfold mid_ss in HS; norm_ss HS.
psrr_branch_tok RUN BR HS SHOK Bspan.
- let Ex := henv Hc in rewrite (h2_blt_op Ex 535 op ltac:(hew; reflexivity) Hop) in Hc. apply Z.leb_le in Hc. rename Hc into HOP.
  htail RUNTO RUN BR Hop cx h i n now op dt fq ly3 S3 W mem3 acc.
- let Ex := henv Hc in rewrite (h2_blt_op Ex 535 op ltac:(hew; reflexivity) Hop) in Hc. apply Z.leb_gt in Hc. rename Hc into HOP.
  htail RUNTO RUN BR Hop cx h i n now op dt fq ly3 S3 W mem3 acc.
Qed.
End h.
End f.
End d.
