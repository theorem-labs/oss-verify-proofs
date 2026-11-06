(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 370 of its 431 lines of code are new or changed and 4992 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a5_tl.v, with its module paths and module names changed; 440 of its 516 lines of code are new or changed and 355 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the piece HDR of segment B7 of
   reac_segconf_parse_file's walk, b7hdr_ok : B7_S_HDR B (lib/B/Prog/pf_seg_B7_m.v: HA_HREF n -> HA_CLOSE n ->
   H_HDR n). The B7 segment lane of the image-B G3 walk owner (a sub-lane), 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, piece HDR of segment B7).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s):
     HDR 0x883b4 li a1,93; 0x883b8 mv a0,s7 (s7 = lp, the trimmed line in buf); 0x883bc jal strchr (trampoline
         SS___interceptor_trampoline_strchr); return 0x883c0 (B7H_RET)
     0x883c0 beqz a0,0x884a0       not found: 0x884a0 auipc a0 / 0x884a4 addi a2 = .str.4 0x21400 (listing object
                                   39 = seg_litA_rc F_notclosed) / 0x884a8 j HREF 0x885ec
     0x883c4 li s11,9; 0x883c8 li s8,32
     0x883cc beq a0,s10,0x891c8    UBSan trap T10 (s10 = -1): decided not taken by the executor from the seed's range
                                   facts a0 in [4096, 2 ^ 47 - 16] (a0 = lp + ci inside buf) and s10 = 2 ^ 64 - 1
     0x883d0 addi a1,a0,1; 0x883d4 srli; 0x883d8 add s4 (SHADOW_OFF); 0x883dc lb; 0x883e0 bnez -> 0x88f90-0x88f98
                                   inline check B#8 (load1 of close[1]; slow arm 0x88f90 / 0x88f94, error call
                                   0x8926c-0x89270 errpath_load1): the token executor's obligation that close + 1 is
                                   addressable, from pf_seg_B7_d.v b7_addr_buf (buf's shadow is 0 in scope)
     0x883e4 lbu a1,0(a1)          close[1], a fresh seed atom (32)
     0x883e8 beqz a1,0x884cc       the line ends at the ']': CLOSE 0x884cc (pf_seg_B7_m.v B7_CLOSE)
     0x883ec auipc a0 / 0x883f0 addi a2 = .str.5 0x21440 (listing object 38 = seg_litA_rc F_after) / 0x883f4 j HREF
   The proof: a seed at HDR (every register its own atom), one token run to the call, the call by aj_art_at with
   RtSeg.astrchr_realizes (premises from pf_seg_B7_r.v b7_strchr_pre_883bc), the cut b7h_ret at the return state
   (pf_base by pf_seg_B7_k.v b7k_base_move: the run writes nothing and strchr only its window below s1), and from
   there two seeds: a0 = 0 (b7h_none: one run to HREF, the step pf_seg_B7_f.v b7_hdr_notclosed), a0 = lp + ci with
   close[1] as a region on a0's atom (b7h_some: one run through T10 and check B#8 to the `beqz a1`, then CLOSE, or
   HREF with b7_hdr_after).
   Instructions walked: 0x883b4 .. 0x883f4 (17), 0x884a0 .. 0x884a8 (3); the check stub's slow arm 0x88f90 /
   0x88f94 is covered by the executor's check token (never reached when the obligation holds); the trap's target
   0x891c8 and the error call 0x8926c-0x89270 are unreachable (T10 decided, check B#8 discharged).
   Section hypotheses: VRO and SSPX (pf_seg_B7_k.v b7k_base_move after the strchr call and after each run), OBJ (the
   two literal atoms A_OBJ 38 / 39), TL (PALib: the errno cell aj_art_at needs), ASTRCHR (the strchr carrier). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require reac_segconf_parse.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B7_f pf_seg_B7_d
  pf_seg_B7_r pf_seg_B7_k pf_seg_B7_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
(* strchr's return 0x883c0, as a listing offset (BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B7H_RET : Z := AF_reac_segconf_parse_file + 0x588.
(* s10 = -1 as an unsigned word *)
Definition B7H_M1 : Z := 18446744073709551615.
(* the registers no instruction of the piece writes: pf_fi's (sp, gp, tp, s0, s1, s4), PF_RL's (s2, s5, s10),
   PF_RM's (s9, s6), and s7 = lp *)
Definition b7h_kept : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 25; 26].
(* at CLOSE also a0 = lp + ci *)
Definition b7h_keptC : list Z := 10 :: b7h_kept.

Lemma b7h_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Ltac b7h_in := solve [cbn [In app]; repeat first [left; reflexivity | right]].
Lemma b7h_bvr : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b7h_bvr' : forall rr (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b7h_nth_app0 : forall (l : list Z) i, nth i (l ++ [0]) 0 = nth i l 0.
Proof.
intros l i. destruct (Nat.lt_ge_cases i (length l)) as [H|H].
- rewrite app_nth1 by exact H. reflexivity.
- rewrite app_nth2 by exact H. rewrite (nth_overflow l) by exact H.
  destruct (i - length l)%nat as [|[|k]]; reflexivity.
Qed.
Lemma b7h_br_eq0 : forall E n v b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = b -> (v =? 0) = b.
Proof.
intros E n v b H Hv Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by lia. exact Hc.
Qed.
Lemma b7h_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma b7h_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v ->
  ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* a register of the state after a run, as the executor wrote it *)
Ltac b7h_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b7h_awr := lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ---------- the seeds ---------- *)
(* at HDR: every register its own atom, no region, no fact *)
Definition b7h_ss_hdr : sstate := mkSS PF_HDR sr_atoms [] None (mkFacts [] [] []).
(* at the return, strchr found nothing: a0 = 0 pinned (the `beqz a0` is decided taken) *)
Definition b7h_ss0 : sstate := mkSS B7H_RET (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
(* at the return, strchr found the ']' at ci: a0 = lp + ci (atom 10, range fact: decides `beqz a0` and the trap T10
   against s10 = 2 ^ 64 - 1, atom 26), s4 = SHADOW_OFF (atom 20, the check's shadow base), close[1] = atom 32, the one
   read-only region [1, 2) on a0's atom *)
Definition b7h_regions1 : smem := [ YP09.mkRegion (Some 10%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))] ].
Definition b7h_facts1 : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 16) 0); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (26%nat, mkAF B7H_M1 B7H_M1 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition b7h_ss1 : sstate := mkSS B7H_RET sr_atoms b7h_regions1 None b7h_facts1.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis TL : PALib B.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).

(* after a run that writes nothing: the environment agrees with the seed's E0 below 33 (HAE), the memory is the
   seed's (KM) *)
Ltac b7h_after E0 HAE KM :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo _ (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in
    assert (HAEn : env_agree 33 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H _) (ms_mem msn) a = aview SEGS (w_H _) _ a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          rewrite (kept_of_frame (segs := SEGS) Eo _ _ m0 (ms_mem msn) (fun _ => False) HFr);
          [ exact (KM a Ha)
          | let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
            intros b wlo whi a' Hin Hrr; vm_compute in Hin;
            repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
            destruct Hin
          | exact Ha | tauto ]);
    clear HAE KM; rename HAEn into HAE; rename KMn into KM;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
  end.

(* the two literals of the refusals: listing objects 38 (.str.5, 0x21440) and 39 (.str.4, 0x21400) *)
Lemma b7h_lit_after : forall E, img_env VAL A_LIM E -> ew E 279%nat = w64 (seg_litA_rc F_after).
Proof.
intros E HE. rewrite (img_env_atomP E 279%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 279%nat with (A_OBJ 38). rewrite (OBJ 38%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma b7h_lit_notclosed : forall E, img_env VAL A_LIM E -> ew E 280%nat = w64 (seg_litA_rc F_notclosed).
Proof.
intros E HE. rewrite (img_env_atomP E 280%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 280%nat with (A_OBJ 39). rewrite (OBJ 39%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run (fx := fx) B LAWS.
Let RUNTO := paj_run_to (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).
(* the seed of the found arm *)
Lemma b7h_seed1 : forall (W : world SEGS) (rX : bvmap 5 word) memc a0 C,
  getr rX (Z_to_bv 5 10) = w64 a0 -> getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 26) = w64 (-1) ->
  4096 <= a0 <= 2 ^ 47 - 16 -> 0 <= C <= 255 -> rdW W memc (a0 + 1) = Some C ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [Z_to_bv 64 C])) b7h_ss1
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + B7H_RET)) memc (seg_rom SEGS))).
Proof.
intros W rX memc a0 C H10 H20 H26 Ha0 HC HrdC.
set (E := Eimg (Ereg rX [Z_to_bv 64 C])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E10 : ew E 10 = Z_to_bv 64 a0) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact H20).
assert (U26 : bv_unsigned (ew E 26) = B7H_M1).
{ rewrite (EE 26%nat (Z_to_bv 5 26) eq_refl), H26. unfold w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 C)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold b7h_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b7h_regions1. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
  unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
  destruct (aview_byte SEGS (w_H W) memc (a0 + 1) C HrdC) as (b & Hb & Hv & _).
  exists b. split.
  + cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E32.
    rewrite !Z.add_0_r. rewrite !(unsigned_lit_small C) by lia. change (8 * 0) with 0. rewrite Z.shiftr_0_r.
    subst C. apply Z_to_bv_bv_unsigned.
  + rewrite !Z.add_0_r. exact Hb.
- cbn. tauto.
- split; [|split; exact I].
  cbn [b7h_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U26, E10, E20, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold B7H_M1, SHADOW_OFF. repeat split; lia.
Qed.


(* b7_st (pf_seg_B7_d.v) from a cut's pf_base *)
Lemma b7h_st_of_base : forall v pos lyc Sc Wc rX memc mdc,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE -> b7_st B v pos lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc (HCX & HFI & HOBJ & _ & HFSH).
destruct HFI as (HJ & Hly & _ & HP & _).
constructor; assumption.
Qed.
(* pf_base at the same frame state, at a later memory that agrees below alloc_ceiling and from s1 up, with the six
   registers of pf_fi kept *)
Lemma b7h_base_keep : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc',
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall r, In r [2; 3; 4; 8; 9; 20] -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' PF_SC_LINE.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' HB HJ' K KR.
apply (b7k_base_move B VRO SSPX fx v pos lyc Sc Wc rX memc mdc PF_SC_LINE lyc Sc Wc rX' memc' mdc' HB
  (fxrel_refl fx) HJ' eq_refl).
- exists (st_fs Sc). destruct Sc; reflexivity.
- apply Permutation_refl.
- exact (b7k_keeps_low B v pos lyc Sc Wc rX memc mdc PF_SC_LINE Wc memc' HB K).
- exact KR.
Qed.
(* c and cur_name at such a later memory *)
Lemma b7h_st0_keep : forall v pos lyc Sc Wc rX memc mdc memc' cf nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LINE ->
  (forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_st0 v pos (rdW Wc memc) cf nm k -> pf_st0 v pos (rdW Wc memc') cf nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc memc' cf nm k HB K (HRC & HNM & HCNT).
pose proof HB as (HCX & HFI & HOBJ & _).
destruct (b7k_frame B v pos lyc Sc Wc rX memc mdc HFI) as (_ & HF4 & HFc & _).
pose proof (proj1 (proj1 HFI)) as HAR.
destruct HOBJ as (_ & _ & _ & _ & HC & _).
destruct (b7k_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HC
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in HFc.
split; [|split; [|exact HCNT]].
- apply (reac_segconf_parse.sa_rconf_low _ _ _ _ HRC); [lia | lia |]. intros a Ha. apply K; lia.
- apply (b7k_nm_move v pos _ _ nm HNM). intros a Ha. change (fs_frame_bytes 5) with 2048 in Ha. apply K; lia.
Qed.

(* the cut at strchr's return 0x883c0: the line's core, the trimmed line at lp, and a0 = strchr's answer *)
Definition b7h_ret (n : nat) (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (cf : rconf) (nm : list Z)
  (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (r : option nat) : Prop :=
  b7_core B n v pos lyc Sc Wc rX memc mdc cf nm o ln d /\
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) /\ pf_inb (pf_F v pos + PF_O_BUF) lp (pf_tline (p_s v) o) /\
  hd0 (pf_tline (p_s v) o) = LBR /\ strchr (pf_tline (p_s v) o) RBR = r /\
  pf_rg rX [(23, lp); (10, match r with None => 0 | Some ci => lp + Z.of_nat ci end)].

(* ---------- not found: 0x883c0 -> 0x884a0 .. 0x884a8 -> HREF, F_notclosed ---------- *)
Lemma b7h_none : forall n, HA_HREF B n -> forall v pos lyc Sc Wc rX memc mdc cf nm o ln d lp,
  b7h_ret n v pos lyc Sc Wc rX memc mdc cf nm o ln d lp None ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7H_RET) rX memc mdc) (b7_post B v cf nm o ln).
Proof.
intros n HREF v pos lyc Sc Wc rX memc mdc cf nm o ln d lp HR.
destruct HR as (HC & HLS & HLI & HD0 & HSC & HR2).
destruct HC as (HB & HMID & HST0 & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
pose proof (b7h_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST.
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST) as (F1 & F2 & _ & F4).
pose proof asan_consts as (C1 & _).
pose proof HLI as HLI'. unfold pf_inb, PF_O_BUF in HLI'.
unfold PF_RL, PF_RM in HRG.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 0) by (apply (b7h_rg rX _ 10 _ HR2); b7h_in).
(* the seed *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E b7h_ss0
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B7H_RET)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b7h_ss0. apply pa_entry_st_ok_full;
    [| vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]].
  apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  cbn [sv_denot]. apply (b7h_bvr _ 10%bv 10); [reflexivity | exact R10]. }
clearbody E.
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B7H_RET)) with (Z_to_bv 64 (BASE + B7H_RET)).
(* 0x883c0 beqz a0 (taken); 0x884a0 auipc a0; 0x884a4 addi a2 = .str.4; 0x884a8 j HREF *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HREF.
{ b7h_awr. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pose proof (regs_kept_of_st_ok_pi _ _ _ rX [] (map (Z_to_bv 5) b7h_kept) HS HA0 ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
assert (KR := fun r (Hr : In r b7h_kept) => HK (Z_to_bv 5 r) (in_map _ _ _ Hr)).
assert (KL := fun a Ha (_ : a < alloc_ceiling \/ pf_s1 v <= a) => KM a Ha).
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_HREF) rg mm mdx) end.
unfold b7_post. rewrite (b7_hdr_notclosed cf nm (ln + 1) (pf_tline (p_s v) o) HSC).
apply (HREF fx v pos lyc Sc Wc _ _ _ cf nm o ln d F_notclosed (seg_litA_rc F_notclosed)
  [AS (pf_tline (p_s v) o)] lp).
split; [|split; [exact HMID | split; [|split]]].
- apply (b7h_base_keep v pos lyc Sc Wc rX memc mdc _ _ _ HB HJ KL).
  intros r Hr. apply KR. unfold b7h_kept. cbn [In] in Hr |- *. tauto.
- exact (b7h_st0_keep v pos lyc Sc Wc rX memc mdc _ cf nm _ HB KL HST0).
- split; [right; left; reflexivity|]. split; [reflexivity|].
  exists (pf_tline (p_s v) o). split; [reflexivity|]. split; [|exact HLI].
  apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS); [lia | lia |]. intros a Ha. apply KM. lia.
- unfold pf_rg, PF_RL, PF_RM. cbn [app].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  all: try solve [ rewrite KR; [first [apply (b7h_rg rX _ _ _ HRG); b7h_in | apply (b7h_rg rX _ _ _ HR2); b7h_in]
                               | unfold b7h_kept; b7h_in] ].
  b7h_rreg HS. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. apply b7h_lit_notclosed. assumption.
Qed.

(* ---------- found at ci: 0x883c0 .. 0x883e8, then CLOSE or 0x883ec .. 0x883f4 -> HREF, F_after ---------- *)
Lemma b7h_some : forall n, HA_HREF B n -> HA_CLOSE B n -> forall v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci,
  b7h_ret n v pos lyc Sc Wc rX memc mdc cf nm o ln d lp (Some ci) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + B7H_RET) rX memc mdc) (b7_post B v cf nm o ln).
Proof.
intros n HREF HCLOSE v pos lyc Sc Wc rX memc mdc cf nm o ln d lp ci HR.
pose proof HR as (HC & HLS & HLI & HD0 & HSC & HR2).
pose proof HC as (HB & HMID & HST0 & HLEN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
pose proof (b7h_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST.
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST) as (F1 & F2 & _ & F4).
pose proof HTF as (_ & _ & _ & TF4 & _). change (fs_frame_bytes 5) with 2048 in TF4.
pose proof asan_consts as (C1 & _).
pose proof HLI as HLI'. unfold pf_inb, PF_O_BUF in HLI'.
pose proof HLS as ((HZ & HNZ) & _).
assert (Hci : (ci < length (pf_tline (p_s v) o))%nat).
{ pose proof HSC as H. rewrite (strchr_memchr _ RBR HNZ ltac:(lia)) in H. exact (memchr_lt _ _ _ H). }
assert (HrdC : rdW Wc memc (lp + Z.of_nat ci + 1) = Some (nth (S ci) (pf_tline (p_s v) o) 0)).
{ pose proof (HZ (S ci) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
  rewrite b7h_nth_app0 in Hb. rewrite <- Hb. f_equal. lia. }
remember (nth (S ci) (pf_tline (p_s v) o) 0) as C eqn:HCdef.
assert (HC255 : 0 <= C <= 255) by (destruct (aview_byte SEGS (w_H Wc) memc _ _ HrdC) as (_ & _ & _ & Hr); lia).
unfold PF_RL, PF_RM in HRG.
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (lp + Z.of_nat ci)) by (apply (b7h_rg rX _ 10 _ HR2); b7h_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (b7h_rg rX _ 20 _ HRG0); b7h_in).
assert (R26 : getr rX (Z_to_bv 5 26) = w64 (-1)) by (apply (b7h_rg rX _ 26 _ HRG); b7h_in).
(* the seed *)
pose proof (b7h_seed1 Wc rX memc (lp + Z.of_nat ci) C R10 R20 R26 ltac:(lia) HC255 HrdC) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [Z_to_bv 64 C]))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 C]) (Eimg (Ereg rX [Z_to_bv 64 C])))
  by (split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E10 : ew (Eimg (Ereg rX [Z_to_bv 64 C])) 10 = Z_to_bv 64 (lp + Z.of_nat ci))
  by (rewrite (ew_Eimg_Ereg_nat rX _ 10 (Z_to_bv 5 10) eq_refl); exact R10).
assert (E20 : ew (Eimg (Ereg rX [Z_to_bv 64 C])) 20 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (ew_Eimg_Ereg_nat rX _ 20 (Z_to_bv 5 20) eq_refl); exact R20).
assert (E32 : ew (Eimg (Ereg rX [Z_to_bv 64 C])) 32 = Z_to_bv 64 C)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI HA0 E10 E20 E32. generalize (Eimg (Ereg rX [Z_to_bv 64 C])) as E0.
intros E0 HS HEI HA0 E10 E20 E32.
pose proof (env_agree_refl 33 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E0 (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + B7H_RET)) with (Z_to_bv 64 (BASE + B7H_RET)).
(* 0x883c0 beqz a0 (decided); li s11,9; li s8,32; 0x883cc T10 (decided); 0x883d0 .. 0x883e0 check B#8;
   0x883e4 lbu a1 = close[1]; up to 0x883e8 beqz a1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ cbn [ms_mem mkst].
  rewrite (U_atom E0 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom_off E0 10 (lp + Z.of_nat ci) 1 E10) by lia.
  destruct (b7_addr_buf B v pos lyc Sc Wc memc mdc (lp + Z.of_nat ci + 1) 1 HST
    ltac:(unfold b7_buf, PF_O_BUF; lia) ltac:(lia) ltac:(unfold b7_buf, PF_O_BUF; lia)) as (_ & _ & _ & HRA & _).
  exact HRA. }
{ b7h_awr. }
b7h_after E0 HAE KM.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* close[1] = 0: the line ends at the ']'; CLOSE *)
  pose proof (b7h_br_eq0 _ 32 C _ (b7h_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as L0.
  apply Z.eqb_eq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan B7_CLOSE. { b7h_awr. }
  b7h_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX [Z_to_bv 64 C] (map (Z_to_bv 5) b7h_keptC) HS
    (b7h_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (KR := fun r (Hr : In r b7h_keptC) => HK (Z_to_bv 5 r) (in_map _ _ _ Hr)).
  assert (KL := fun a Ha (_ : a < alloc_ceiling \/ pf_s1 v <= a) => KM a Ha).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + B7_CLOSE) rg mm mdx) end.
  apply (HCLOSE fx v pos lyc Sc Wc _ _ _ cf nm o ln d lp ci).
  unfold INV_CLOSE, b7_core.
  split; [split; [|split; [exact HMID | split; [|split; [exact HLEN|]]]]|].
  + apply (b7h_base_keep v pos lyc Sc Wc rX memc mdc _ _ _ HB HJ KL).
    intros r Hr. apply KR. unfold b7h_keptC, b7h_kept. cbn [In] in Hr |- *. tauto.
  + exact (b7h_st0_keep v pos lyc Sc Wc rX memc mdc _ cf nm _ HB KL HST0).
  + unfold pf_rg, PF_RL, PF_RM. cbn [app].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
      (rewrite KR; [apply (b7h_rg rX _ _ _ HRG); b7h_in | unfold b7h_keptC, b7h_kept; b7h_in]).
  + split.
    { apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS); [lia | lia |]. intros a Ha. apply KM. lia. }
    split; [exact HLI|]. split; [exact HD0|]. split; [exact HSC|].
    split; [rewrite <- HCdef; exact L0|].
    unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    * rewrite KR; [apply (b7h_rg rX _ _ _ HR2); b7h_in | unfold b7h_keptC, b7h_kept; b7h_in].
    * rewrite KR; [exact R10 | unfold b7h_keptC, b7h_kept; b7h_in].
    * b7h_rreg HS. reflexivity.
    * b7h_rreg HS. reflexivity.
- (* close[1] <> 0: text after the ']'; HREF with F_after *)
  pose proof (b7h_br_eq0 _ 32 C _ (b7h_ag_ew _ _ _ 32 _ HAE ltac:(lia) E32) ltac:(lia) Hc) as L0.
  apply Z.eqb_neq in L0. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_HREF. { b7h_awr. }
  b7h_after E0 HAE KM.
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX [Z_to_bv 64 C] (map (Z_to_bv 5) b7h_kept) HS
    (b7h_ag32 _ _ _ _ 33 ltac:(lia) HA0 HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  assert (KR := fun r (Hr : In r b7h_kept) => HK (Z_to_bv 5 r) (in_map _ _ _ Hr)).
  assert (KL := fun a Ha (_ : a < alloc_ceiling \/ pf_s1 v <= a) => KM a Ha).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_HREF) rg mm mdx) end.
  unfold b7_post.
  rewrite (b7_hdr_after cf nm (ln + 1) (pf_tline (p_s v) o) ci HSC ltac:(rewrite <- HCdef; exact L0)).
  apply (HREF fx v pos lyc Sc Wc _ _ _ cf nm o ln d F_after (seg_litA_rc F_after) [AS (pf_tline (p_s v) o)] lp).
  split; [|split; [exact HMID | split; [|split]]].
  + apply (b7h_base_keep v pos lyc Sc Wc rX memc mdc _ _ _ HB HJ KL).
    intros r Hr. apply KR. unfold b7h_kept. cbn [In] in Hr |- *. tauto.
  + exact (b7h_st0_keep v pos lyc Sc Wc rX memc mdc _ cf nm _ HB KL HST0).
  + split; [left; reflexivity|]. split; [reflexivity|].
    exists (pf_tline (p_s v) o). split; [reflexivity|]. split; [|exact HLI].
    apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS); [lia | lia |]. intros a Ha. apply KM. lia.
  + unfold pf_rg, PF_RL, PF_RM. cbn [app].
    repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
    all: try solve [ rewrite KR; [first [apply (b7h_rg rX _ _ _ HRG); b7h_in | apply (b7h_rg rX _ _ _ HR2); b7h_in]
                                 | unfold b7h_kept; b7h_in] ].
    b7h_rreg HS. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. apply b7h_lit_after. assumption.
Qed.

(* ---------- HDR 0x883b4 .. 0x883bc: the strchr call, then the two arms ---------- *)
Lemma b7h_hdr : forall n, HA_HREF B n -> HA_CLOSE B n -> H_HDR B n.
Proof.
intros n HREF HCLOSE v pos lyc Sc Wc rX memc mdc cf cur nm o ln d lp HI.
change (pf_postm B v (r_header cf nm (ln + 1) (pf_tline (p_s v) o)) o ln) with (b7_post B v cf nm o ln).
destruct HI as (HB & HMID & HST & HLEN & HLS & HLI & HD0 & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & HTF & _ & HRG0).
pose proof (b7h_st_of_base v pos lyc Sc Wc rX memc mdc HB) as HST0.
destruct (b7_stk B v pos lyc Sc Wc memc mdc HST0) as (G1 & G2 & G3 & G4 & G5 & G6).
destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc HST0) as (F1 & F2 & _ & F4).
destruct (b7k_cx B v HCX) as (_ & _ & _ & _ & _ & _ & H47 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
rewrite SPF in G3.
pose proof asan_consts as (C1 & _).
pose proof HLI as HLI'. unfold pf_inb, PF_O_BUF in HLI'.
assert (HLp0 : 0 <= lp) by lia.
assert (HLp1 : lp + Z.of_nat (length (pf_tline (p_s v) o)) < alloc_ceiling) by lia.
unfold PF_RL, PF_RM in HRG.
(* the seed *)
set (E := Eimg (Ereg rX [])).
assert (HS : st_ok_pi SEGS VAL E b7h_ss_hdr
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_HDR)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b7h_ss_hdr. apply pa_entry_st_ok_full;
    [subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto
    | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS (SOff 20 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_HDR)) with (Z_to_bv 64 (BASE + PF_HDR)).
(* 0x883b4 li a1,93; 0x883b8 mv a0,s7; 0x883bc jal strchr *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ b7h_awr. }
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
clear HFr HG HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
(* the registers at the call *)
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX [] (map (Z_to_bv 5) b7h_kept) HS HA0 ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
prreg HS (1%bv : bv 5) R1. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
pmkst HS.
assert (R2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ apply (b7h_bvr _ 2%bv 2); [reflexivity|].
  rewrite HK; [apply (b7h_rg rX _ 2 _ HRG0); b7h_in | apply in_map; unfold b7h_kept; b7h_in]. }
assert (R3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ apply (b7h_bvr _ 3%bv 3); [reflexivity|].
  rewrite HK; [apply (b7h_rg rX _ 3 _ HRG0); b7h_in | apply in_map; unfold b7h_kept; b7h_in]. }
assert (R4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ apply (b7h_bvr _ 4%bv 4); [reflexivity|].
  rewrite HK; [apply (b7h_rg rX _ 4 _ HRG0); b7h_in | apply in_map; unfold b7h_kept; b7h_in]. }
assert (R23 : getr rX 23 = w64 lp).
{ apply (b7h_bvr _ 23%bv 23); [reflexivity|]. apply (b7h_rg rX _ 23 _ HRG); b7h_in. }
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite R1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (R10' : getr (ms_regs ms) 10 = w64 lp) by (rewrite R10, (EE 23%nat 23%bv eq_refl); exact R23).
pose proof (b7_keep_art B v pos lyc Sc Wc memc mdc (ms_mem ms) mdv 0 0 HST0 HJ ltac:(rewrite SPF; lia)
  (fun a Ha _ _ => KM1 a Ha)) as HST1.
assert (HLS1 : sa_str (rdW Wc (ms_mem ms)) lp (pf_tline (p_s v) o)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS HLp0 HLp1). intros a Ha. apply KM1. lia. }
destruct (b7_strchr_pre_883bc B v pos lyc Sc Wc (ms_mem ms) mdv (ms_regs ms) lp (pf_tline (p_s v) o) HST1
  ltac:(rewrite Hsp; lia) HraT R3 R4 R10' ltac:(rewrite R11; reflexivity) HLS1 HLI)
  as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
(* the call *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low errno_low (2 * ESTACK) (fun _ => False)
    (SIG SS___interceptor_trampoline_strchr) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdv 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B7H_RET)) _ HJ Hsp G6 ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(rewrite SPF; unfold ESTACK; lia) ltac:(rewrite R1; reflexivity) (fun a (H : False) => False_ind _ H)).
  exact (ASTRCHR fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv lp 93 (seg_spec.zb (pf_tline (p_s v) o)) P1 P2 P3 P4 P5
    P6 P7 P8 P9 P10). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B7H_RET)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B7H_RET) regs2 mem2 md2).
(* the memory after the call: the cut's off strchr's window [s1 - 2 * ESTACK, s1), which lies above
   alloc_ceiling *)
assert (KM2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hn. rewrite HK2; [exact (KM1 a Ha) | exact Ha | lia | tauto]. }
assert (KL : forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ pf_s1 v <= a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha Hw. apply KM2; [exact Ha|]. unfold ESTACK. lia. }
(* the registers after the call: the callee-saved ones of the run *)
assert (KPR : forall k, In k b7h_kept -> getr regs2 (Z_to_bv 5 k) = getr rX (Z_to_bv 5 k)).
{ intros k Hk. rewrite (HP2 k).
  - apply HK. apply in_map. exact Hk.
  - unfold b7h_kept in Hk. cbn [In] in Hk. unfold acallee_saved.
    repeat (destruct Hk as [<- | Hk]; [lia |]). destruct Hk. }
assert (HB2 : pf_base B v pos lyc Sc Wc regs2 mem2 md2 PF_SC_LINE).
{ apply (b7h_base_keep v pos lyc Sc Wc rX memc mdc regs2 mem2 md2 HB HJ2 KL).
  intros r Hr. apply KPR. unfold b7h_kept. cbn [In] in Hr |- *. tauto. }
destruct HST as (HRC & _ & HNM & HCNT & _).
assert (HST2 : pf_st0 v pos (rdW Wc mem2) cf nm (length (skipn o (p_s v))))
  by exact (b7h_st0_keep v pos lyc Sc Wc rX memc mdc mem2 cf nm _ HB KL (conj HRC (conj HNM HCNT))).
assert (HLS2 : sa_str (rdW Wc mem2) lp (pf_tline (p_s v) o)).
{ apply (reac_segconf_parse.sa_str_low _ _ _ _ HLS HLp0 HLp1). intros a Ha. apply KL; lia. }
assert (HRG2 : pf_rg regs2 (PF_RL v pos ++ PF_RM v o ln)).
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite KPR; [apply (b7h_rg rX _ _ _ HRG); b7h_in | unfold b7h_kept; b7h_in]). }
assert (R23' : getr regs2 (Z_to_bv 5 23) = w64 lp)
  by (rewrite KPR; [apply (b7h_rg rX _ _ _ HRG); b7h_in | unfold b7h_kept; b7h_in]).
(* strchr's answer, as SegModel's strchr *)
destruct (b7_astr_of_sa Wc (ms_mem ms) lp _ HLS1) as (_ & _ & _ & HZS & _).
pose proof HLS as ((_ & HNZ) & _).
change (map (fun b : byte => bv_unsigned b) (seg_spec.zb (pf_tline (p_s v) o)))
  with (seg_spec.zs (seg_spec.zb (pf_tline (p_s v) o))) in HQ.
rewrite HZS in HQ.
destruct HQ as [(Q0 & Qn) | (j & Qj & Q0)].
- apply (b7h_none n HREF v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d lp).
  split; [split; [exact HB2 | split; [exact HMID | split; [exact HST2 | split; [exact HLEN | exact HRG2]]]]|].
  split; [exact HLS2|]. split; [exact HLI|]. split; [exact HD0|].
  split; [exact (b7_notin_strchr _ 93 HNZ Qn)|].
  unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + exact R23'.
  + apply (b7h_bvr' _ 10%bv 10); [reflexivity | exact Q0].
- apply (b7h_some n HREF HCLOSE v pos lyc Sc Wc regs2 mem2 md2 cf nm o ln d lp j).
  split; [split; [exact HB2 | split; [exact HMID | split; [exact HST2 | split; [exact HLEN | exact HRG2]]]]|].
  split; [exact HLS2|]. split; [exact HLI|]. split; [exact HD0|].
  split; [exact (b7_first_at_strchr _ 93 j HNZ ltac:(lia) Qj)|].
  unfold pf_rg. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  + exact R23'.
  + apply (b7h_bvr' _ 10%bv 10); [reflexivity | exact Q0].
Qed.
End x.

(* the piece of pf_seg_B7_m.v at every FP state *)
Theorem b7hdr_ok : B7_S_HDR B.
Proof. intros f0 n HREF HCLOSE. exact (b7h_hdr (fx := f0) n HREF HCLOSE). Qed.
End d.
