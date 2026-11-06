(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/QPgMain3.v (reseatQ) and QPgRt.v (U_offx) at
   160c9b4d5750, and proofs/libreac/fuzz_knock/lib/A/APgMain4.v (reseatK), APgStep.v and APgRt.v (upd_aboveW) at
   6ebe35ba632; adapted to the row loop of reac_box_pin_parse (the strlen and strncmp wrapper calls). *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec PPgWrap PPgParseCx PPgParseLib PPgParse2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* reac_box_pin_parse of reac-pw/fuzz_pin's ASan image A: the row loop 0x80cc0 .. 0x80cfc and its exit
   0x80d00 .. 0x80d98. pp_seg2L (PPgParseCx.v's PP_seg2L) is closed by induction on the rows left (11 - i)
   over two cut states: ss_PL (the loop head at row i) and ss_PN (0x80cec, row i is not the spec's token).
   pp_row walks one row: the instrumented check of the row's first 8 bytes, the strlen and strncmp wrapper
   calls, the two branches. pp_next walks 0x80cec: the back edge to row i + 1, or after row 10 the refusal. *)

(* ===================== 1. the row scan, as the loop runs it ===================== *)
(* No row before i holds the token, so the first-match scan from 0 is the scan from i. *)
Lemma pl_row_from_skip : forall i t, (i <= CAT_N)%nat -> (forall j, (j < i)%nat -> tok_bytes j <> t) ->
  row_of t = row_from i t.
Proof.
  induction i as [|i IH]; intros t Hi Hj; [reflexivity|].
  rewrite (IH t ltac:(lia) ltac:(intros j Hj'; apply Hj; lia)).
  rewrite (row_from_step i t ltac:(unfold CAT_N in *; lia)).
  destruct (bytes_eqb (tok_bytes i) t) eqn:E; [|reflexivity].
  apply bytes_eqb_eq in E. exfalso. exact (Hj i ltac:(lia) E).
Qed.
(* `beqz a0` at 0x80ce8 taken at row i: the token of row i is the spec's, no earlier row's is. *)
Lemma pl_row_found : forall s i, (i < CAT_N)%nat -> tok_bytes i = pin_token s ->
  (forall j, (j < i)%nat -> tok_bytes j <> pin_token s) -> pin_row s = Some i.
Proof.
  intros s i Hi Ht Hj. unfold pin_row.
  rewrite (pl_row_from_skip i _ ltac:(lia) Hj), (row_from_step i _ Hi), Ht, bytes_eqb_refl. reflexivity.
Qed.

(* ===================== 2. the row addresses the back edge moves ===================== *)
Lemma pl_row_addr_S : forall cat i, row_addr cat (S i) = row_addr cat i + 0x128.
Proof. intros cat i. unfold row_addr, CAT_ROW. lia. Qed.
Lemma pl_row_in : forall cat i, (i < CAT_N)%nat -> cat <= row_addr cat i /\ row_addr cat i + 16 <= cat + CAT_BYTES.
Proof. intros cat i Hi. unfold row_addr, CAT_ROW, CAT_BYTES, CAT_N in *. lia. Qed.

(* ===================== 3. the next-row cut and the closure =====================
   The two paths that leave row i without a match (0x80cd4 `bne` taken after the strlen call, 0x80ce8 `beqz`
   not taken after the strncmp call) meet at 0x80cec. ss_PN is ss_PL_0 with its pc moved there: the same live
   registers (s3 rows left, s5 sa, s6 the row's shadow address, s7 = s8 the row, s9 toklen), the same regions and
   facts. Its dead registers take their own window PW_PN = 260 (17 atoms, 260..276): the back edge joins ss_PN's
   state into ss_PL with no call between them, so ss_PN's dead atoms must miss ss_PL's window 280..296; and
   260..276 misses ss_P3's window 240..258 and ss_P4's 200..223. INV_PN i adds to INV_PL i that row i's token is
   not the spec's. *)
Definition PW_PN : nat := 260.
Definition ss_PN : sstate := Eval vm_compute in
ss_havoc_regs (mkSS 0x80cec (ss_regs ss_PL_0) (ss_mem ss_PL_0) None (ss_facts ss_PL_0)) PW_PN pp_deads_PL.
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Definition INV_PN (B : asyms) (MT : ameter_ops) (RLO RHI cat : Z) (TP DP : nat -> Z) (i : nat) : ppinv :=
fun cx E lyN SN WN msN mdN =>
INV_PL B MT RLO RHI cat TP DP i cx E lyN SN WN msN mdN /\ tok_bytes i <> pin_token (c_s cx).
End i.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Local Notation PF := (pp_from B MT RLO RHI cat TP DP).
Local Notation IPL := (INV_PL B MT RLO RHI cat TP DP).
Local Notation IPN := (INV_PN B MT RLO RHI cat TP DP).
(* 0x80cc0 .. 0x80ce8: row i's check, its token, the strlen and strncmp calls -> ss_P3 (found) or ss_PN *)
Hypothesis RROW : forall i, PF ss_P3 (INV_P3 B MT RLO RHI cat TP DP) -> PF ss_PN (IPN i) -> PF ss_PL (IPL i).
(* 0x80cec .. 0x80cfc: the next row -> ss_PL at i + 1, or after row 10 0x80d00 .. 0x80d98 -> ss_P4 *)
Hypothesis RNEXT : forall i, PF ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
  ((S i < CAT_N)%nat -> PF ss_PL (IPL (S i))) -> PF ss_PN (IPN i).
(* the loop, closed by induction on the rows left: at CAT_N - i = 0 the head is unreachable (INV_PL asks
   i < 11), at S n one row is one pass and the induction hypothesis is the next row *)
Lemma pp_loop : PF ss_P3 (INV_P3 B MT RLO RHI cat TP DP) -> PF ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
forall i, PF ss_PL (IPL i).
Proof.
intros R3 R4.
assert (H : forall n i, (CAT_N - i)%nat = n -> PF ss_PL (IPL i)).
{ induction n as [|n IH]; intros i Hn.
  - intros cx E lyN SN WN msN mdN _ _ _ _ _ _ _ _ _ HINV _. exfalso.
    destruct HINV as (_ & _ & Hi & _). unfold CAT_N in *. lia.
  - apply (RROW i R3). apply (RNEXT i R4). intros Hlt. apply IH. unfold CAT_N in *. lia. }
intros i. exact (H _ i eq_refl).
Qed.
End d.

(* ===================== 4. the read-only objects at the memory of the loop =====================
   The contract's F-RO-LAW (pin_ro_law) gives the table and the ':' set in EVERY state of the allocator relation
   whose read-only bytes read as the image; pp_arodata_kept (PPgParseCx.v) carries that second fact along the
   kept-memory fact, under the Section hypothesis RELRO that the [RLO, RHI) window is image memory. *)
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
(* pin's .data.rel.ro start .. .got end; the close discharges it from the section headers *)
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Lemma pl_ro_now : forall (W : world tfibsegs) (memc : word -> option byte) lyc Sc slo shi (Er : Z -> Prop)
  (WN : world tfibsegs) memN STK2 sp2 FP2 ly2 S2 (W02 : world tfibsegs) mem02 md02 own2 lyN SN mdN k2,
arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc) ->
pin_ro_law tfibsegs B RLO RHI cat TP DP PP_COLON ->
acall_kept tfibsegs B lyc Sc W memc WN memN slo shi Er ->
ajournal tfibsegs B STK2 sp2 FP2 ly2 S2 W02 mem02 md02 own2 lyN SN WN memN mdN k2 ->
pin_cat_ok tfibsegs (mrestrict (w_H WN) memN) (aview tfibsegs (w_H WN) memN) cat TP DP /\
pin_ro_str tfibsegs (mrestrict (w_H WN) memN) (aview tfibsegs (w_H WN) memN) PP_COLON pin_colon_bytes.
Proof.
intros W memc lyc Sc slo shi Er WN memN STK2 sp2 FP2 ly2 S2 W02 mem02 md02 own2 lyN SN mdN k2 HROD HL HKE HJ.
eapply (pin_ro_law_at tfibsegs B RLO RHI cat TP DP PP_COLON); [exact HL | exact HJ |].
eapply (pp_arodata_kept B RLO RHI lyc Sc W memc WN memN slo shi Er); [exact RELRO | exact HKE | exact HROD].
Qed.
(* the read-only premise of a wrapper call at the loop's memory *)
Lemma pl_aro_now : forall (W : world tfibsegs) memc lyc Sc slo shi (Er : Z -> Prop) (WN : world tfibsegs) memN,
arodata_okP tfibsegs RLO RHI B (aview tfibsegs (w_H W) memc) ->
acall_kept tfibsegs B lyc Sc W memc WN memN slo shi Er ->
aro_unowned tfibsegs B (aview tfibsegs (w_H WN) memN).
Proof.
intros W memc lyc Sc slo shi Er WN memN HROD HKE.
exact (pp_aro_kept tfibsegs B lyc Sc W memc WN memN slo shi Er
  (aro_unowned_of_arodataP tfibsegs B RLO RHI _ HROD) HKE).
Qed.
End h.

(* ===================== 5. the tactics and the denotations of the row loop =====================
   PPgParseCx.v carries the ported knock tactics (ewpeel, add_atom_win, pin_by, ra_join_win, pp_run_to,
   pp_br, ppAWR, ppKEPT, pp_hand, pp_fs_rw / pp_fs_ro); only what the row loop needs beyond them is here. *)
(* an atom's fact with the alignment the cut state asks for, over the afact_ok components *)
Ltac add_factA HS n f tac :=
add_fact HS n f ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; tac).
(* the same with the plain symbolic runner: the store of the count cell's shadow byte needs the frame's
   shadow region writable, which the token runner's shadow entries do not allow *)
Ltac pl_run_sh HS HJ AG fpos F EFA stop :=
aj_run_to_sh tfibtbl_lib_ok HS HJ stop;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => ppAWR AG fpos F EFA ltac:(fail) end).
(* [qdisc A/QPgMain3.v:97-120 reseatQ, knock A/APgMain4.v:149-178 reseatK] the state after a call: the
   clobbered registers take junk atoms from the floor K, the kept regions are proved kept by kept_tac, and
   the equation of the re-seated valuation is kept as HEv (the callee's result sits in the junk atom of a0,
   K + 4, which only that equation names) *)
Ltac pl_reseat HS K HJ2 HP2 keep AG kept_tac HEv :=
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac
| specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by (clear - Hnn; lia);
    rewrite ?ew_ewset_other by (clear - Hnn; lia); apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by nat_side; rewrite ?ew_ewset_other by nat_side; exact H);
clear H; rename H2 into H
end end end;
clear AG; rename AG2 into AG end end.

(* [qdisc A/QPgRt.v:167-168, knock A/APgStep.v:77-78] a branch condition on an offset of an atom *)
Lemma U_offx : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> U E (SOff n c) = (x + c) mod 2 ^ 64.
Proof. intros E n x c Hn Hx. rewrite U_SOff, Hn, unsigned_lit_small by lia. reflexivity. Qed.
Ltac hc_off H n v c En :=
lazymatch type of H with context [U ?E' (SOff n c)] =>
rewrite (U_offx E' n v c ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En) ltac:(lia)) in H end.

(* `srli x,x,3` of a 64-bit value *)
Lemma pl_srl3 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_SRL (SOff n 0) (SLit 3)) = v / 8.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n v Hn Hv), U_SLit.
replace (Z.land (zcanon 3) 63) with 3 by (vm_compute; reflexivity).
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound v 8 v ltac:(lia) ltac:(lia)).
apply zcanon_id. unfold M64. lia.
Qed.
(* 0x80cf4 `addi s6,s6,0x25`: the shadow address of the next row, from that of row i *)
Lemma pl_s6_next : forall E n m row,
ew E 32 = Z_to_bv 64 SB -> ew E n = Z_to_bv 64 row -> ew E m = Z_to_bv 64 (row + 296) ->
0 <= row -> row + 296 < 2 ^ 47 -> row mod 8 = 0 ->
sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m 0) (SLit 3)))
= sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) (SLit 37)).
Proof.
intros E n m row E32 En Em H0 H47 H8.
assert (Hd : (row + 296) / 8 = row / 8 + 37)
  by (replace (row + 296) with (row + 37 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
assert (Hlb : 0 <= row / 8) by (apply Z.div_pos; lia).
assert (Hub : row / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite !denot_lit_U. f_equal.
rewrite (U_SAlu E ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m 0) (SLit 3))).
rewrite (U_SAlu E ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) (SLit 37)).
rewrite (U_SAlu E ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))).
cbn [zalu_raw].
rewrite (pl_srl3 E m (row + 296) Em ltac:(lia)), (pl_srl3 E n row En ltac:(lia)).
rewrite (U_atom E 32 SB E32 ltac:(unfold SB; lia)), U_SLit.
rewrite Hd. unfold zcanon, M64.
rewrite (Z.mod_small (SB + row / 8) (2 ^ 64)) by (unfold SB; lia).
rewrite (Z.mod_small 37 (2 ^ 64)) by lia.
f_equal. lia.
Qed.
(* the same shadow address read off another atom of the same value (the back edge re-seats the row) *)
Lemma pl_s6_same : forall E n m, ew E n = ew E m ->
sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff n 0) (SLit 3)))
= sv_denot E (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff m 0) (SLit 3))).
Proof. intros E n m H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

(* a byte outside every writable window of the state is unchanged by a run [knock A/APgRt.v's upd_aboveW,
   lib/A/ACep.v:60-66 aview_kept_frame with one address] *)
Lemma pl_aview_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* every writable byte of a state of this walk is in the call's stack window or in the own frame *)
Ltac pl_inzone AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end;
cbn [In] in Hin;
unfold pp_nf, SHADOW_OFF; try (change T_parse_STK with 8400);
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg;
  first [ left; lia | right; left; lia | right; right; left; lia | exfalso; lia ] | ]);
destruct Hin.
(* the kept-memory fact after a run of the walk's own code: every byte the run may change is in the call's
   stack window or in the class-0 frame (PPgParseLib.v's pp_KE_step, grant's pz_kept_own).  The names it
   reads are the ones pp_prelude leaves, plus HslC / HshC / HOCF / HlyF of the segment's own prelude. *)
Ltac pl_kept AG Zs HAR0x HfrsX HPERMx HlyFx FFLx HslCx HshCx HOCFx :=
lazymatch goal with
| HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msX)),
  HGx : mem_grows (mrestrict _ _) (mrestrict _ (ms_mem ?msX)),
  HKEx : acall_kept ?sg ?Bv ?lycx ?Scx ?Wx ?memcx ?WXx ?memXx ?slox ?shix ?Eox |- _ =>
let HK2 := fresh "HKE2" in let HARx := fresh "HARx" in let L := rnLAWS in
assert (HK2 : acall_kept sg Bv lycx Scx Wx memcx WXx (ms_mem msX) slox shix Eox);
[ pose proof (proj1 HJx) as HARx;
  eapply (pp_KE_step _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Zs);
  [ exact HAR0x | exact HARx | exact HfrsX | exact HPERMx | exact HlyFx | reflexivity | reflexivity
  | exact FFLx | exact HslCx | exact HshCx | exact HOCFx
  | let aa := fresh "a" in let Ha := fresh "Ha" in intros aa [Ha|Ha]; [left; exact Ha | right; right; exact Ha]
  | exact HKEx
  | let aa := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in let Hw := fresh "Hw" in
    intros aa Ha Hn; eapply pl_aview_frame; [exact HFrx | exact Ha | intros Hw; apply Hn; revert Hw; pl_inzone AG]
  | let aa := fresh "a" in let Hp := fresh "Hp" in intros aa _ Hp; exact (apresent_grows _ _ _ aa HGx Hp) ]
| clear HKEx; rename HK2 into HKEx; clear_frames ]
end.
(* the same after a wrapper call, whose post keeps every byte outside its own stack window *)
Ltac pl_kept_call HJx Hfrc Hprc Zs HAR0x HfrsX HPERMx HlyFx FFLx HslCx HshCx HOCFx :=
lazymatch goal with
| HKEx : acall_kept ?sg ?Bv ?lycx ?Scx ?Wx ?memcx ?WXx ?memXx ?slox ?shix ?Eox |- _ =>
lazymatch type of Hfrc with forall a, _ -> _ -> aview _ _ ?memY a = _ =>
let HK2 := fresh "HKE2" in let HARx := fresh "HARx" in let L := rnLAWS in
assert (HK2 : acall_kept sg Bv lycx Scx Wx memcx WXx memY slox shix Eox);
[ pose proof (proj1 HJx) as HARx;
  eapply (pp_KE_step _ L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Zs);
  [ exact HAR0x | exact HARx | exact HfrsX | exact HPERMx | exact HlyFx | reflexivity | reflexivity
  | exact FFLx | exact HslCx | exact HshCx | exact HOCFx
  | let aa := fresh "a" in let Ha := fresh "Ha" in intros aa Ha; left; change T_parse_STK with 8400; lia
  | exact HKEx
  | let aa := fresh "a" in intros aa; apply Hfrc
  | let aa := fresh "a" in let Hp := fresh "Hp" in intros aa _ Hp; exact (Hprc aa Hp) ]
| clear HKEx; rename HK2 into HKEx ] end end.

(* ===================== 6. 0x80cec: the next row, or the exit after row 10 ===================== *)
Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.

(* 0x80cec addi s3,s3,-1 / addi s8,s8,0x128 / addi s6,s6,0x25 / addi s7,s7,0x128 / 0x80cfc bnez s3,0x80cc0;
   not taken (row 10 was the last): 0x80d00 a3 = -1, `j 0x80d94`, the count cell's shadow byte back to 0xf8. *)
Lemma pp_next : forall i,
pp_from B MT RLO RHI cat TP DP ss_P4 (INV_P4 B MT RLO RHI cat TP DP) ->
((S i < CAT_N)%nat -> pp_from B MT RLO RHI cat TP DP ss_PL (INV_PL B MT RLO RHI cat TP DP (S i))) ->
pp_from B MT RLO RHI cat TP DP ss_PN (INV_PN B MT RLO RHI cat TP DP i).
Proof.
intros i R4 RL. pp_prelude.
destruct HINV as (HPL & Hne). red in HPL.
destruct HPL as (Hlv & Hsne & Hi & Etl & Erow & Ecnt & Hprev).
unfold PN_tl, PN_row, PN_cnt in Etl, Erow, Ecnt.
assert (HiZ : 0 <= Z.of_nat i <= 10) by (clear - Hi; unfold CAT_N in Hi; lia).
pose proof Hcat as (Hcat0 & Hcat8 & Hcat63 & Hcatamr & Hcatra & Hrows).
assert (Hrow8 : row_addr cat i mod 8 = 0) by (apply row_addr_mod8; exact Hcat8).
assert (Hamr : cat + CAT_BYTES <= 2 ^ 47 - 1)
  by (clear - Hcatamr; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hcatamr; lia).
assert (Hrowlo : 0 < row_addr cat i) by (apply row_addr_pos; exact Hcat0).
assert (Hrowhi : row_addr cat i + 16 <= cat + CAT_BYTES) by exact (proj2 (pl_row_in cat i Hi)).
pose proof (pp_oc_frames_of_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sa mo lb s
  cidm posm cidl posl HJ0 Hlive) as HOCF.
assert (HslC : alloc_ceiling <= spZ regs - T_parse_STK)
  by (change T_parse_STK with 8400; clear - Hceil Hslo HspLo; lia).
assert (HshC : spZ regs <= 2 ^ 64) by (clear - Hshi HspHi H47; lia).
assert (HlyF : ly_F lyN = ly_F lyc) by exact (pp_lyF B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  STK sp0 FP W0 mem0 md0 ((0, fpos) :: own) lyN SN WN (ms_mem msN) mdN k HJ0 HJ).
(* 0x80cec .. 0x80cf8, then the back-edge branch *)
pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80cfc.
(* the run wrote nothing outside the call's stack window and the own frame *)
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
rebaseE HS AG HEv. clear HEv.
ppLOW HS AG E32 E32n.
pp_br HS Hc.
{ (* taken: 11 - i - 1 <> 0, so row i was not row 10: the back edge to 0x80cc0 at row i + 1 *)
  (* `hc_off` and `lia` need the row index as a Z bound; CAT_N is a Definition *)
  hc_bool Hc ltac:(fun H => hc_off H 103%nat (11 - Z.of_nat i) (-1) Ecnt). hc_prop Hc.
  rewrite Z.mod_small in Hc by (clear - Hi; unfold CAT_N in Hi; lia).
  assert (HiS : (Datatypes.S i < CAT_N)%nat) by (clear - Hi Hc; unfold CAT_N in *; lia).
  specialize (RL HiS).
  pose proof (pl_row_addr_S cat i) as HrS.
  assert (HrowSlo : 0 < row_addr cat (Datatypes.S i)) by (apply row_addr_pos; exact Hcat0).
  assert (HrowShi : row_addr cat (Datatypes.S i) + 16 <= cat + CAT_BYTES)
    by exact (proj2 (pl_row_in cat (Datatypes.S i) HiS)).
  assert (HrowS8 : row_addr cat (Datatypes.S i) mod 8 = 0) by (apply row_addr_mod8; exact Hcat8).
  pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80cc0.
  pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
    HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
  rebaseE HS AG HEv. clear HEv.
  ppLOW HS AG E32 E32n.
  (* the next row and the rows left, first in scratch atoms, so that 102 and 103 become free *)
  add_atom_win HS 400%nat (Z_to_bv 64 (row_addr cat (Datatypes.S i))) E400.
  pin_by HS (23%bv : bv 5) (SOff 400 0)
    ltac:(rewrite sv_denot_SOff0, E400; cbn [sv_denot]; ewpeel; rewrite Erow, unsigned_lit_small by lia;
          f_equal; lia).
  pin_by HS (24%bv : bv 5) (SOff 400 0)
    ltac:(rewrite sv_denot_SOff0, E400; cbn [sv_denot]; ewpeel; rewrite Erow, unsigned_lit_small by lia;
          f_equal; lia).
  pin_by HS (22%bv : bv 5) (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 400 0) (SLit 3)))
    ltac:(apply (pl_s6_next _ 102%nat 400%nat (row_addr cat i));
          [ewpeel; exact E32n | ewpeel; exact Erow | ewpeel; rewrite E400, HrS; f_equal; lia
          | lia | lia | exact Hrow8]).
  add_atom_win HS 401%nat (Z_to_bv 64 (11 - Z.of_nat (Datatypes.S i))) E401.
  pin_by HS (19%bv : bv 5) (SOff 401 0)
    ltac:(rewrite sv_denot_SOff0, E401; cbn [sv_denot]; ewpeel; rewrite Ecnt, unsigned_lit_small by lia;
          f_equal; lia).
  (* the facts of the two reused atoms, and the branch condition on 103, are dropped *)
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (List.filter (fun p : nat * afact => win_free 102 2 (fst p)) (f_atoms (ss_facts ssx))) in
    let cs := eval vm_compute in (List.filter (cond_atoms_on (win_free 102 2)) (f_conds (ss_facts ssx))) in
    let al := eval vm_compute in (f_alias (ss_facts ssx)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cs al HS
      ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end.
  norm_ss HS. clear Erow Ecnt.
  add_atom_win HS 102%nat (Z_to_bv 64 (row_addr cat (Datatypes.S i))) Erow.
  pin_by HS (23%bv : bv 5) (SOff 102 0)
    ltac:(rewrite !sv_denot_SOff0, Erow; ewpeel; rewrite E400; reflexivity).
  pin_by HS (24%bv : bv 5) (SOff 102 0)
    ltac:(rewrite !sv_denot_SOff0, Erow; ewpeel; rewrite E400; reflexivity).
  pin_by HS (22%bv : bv 5) (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SOff 102 0) (SLit 3)))
    ltac:(apply pl_s6_same; rewrite Erow; ewpeel; rewrite E400; reflexivity).
  add_factA HS 102%nat (mkAF 0 (2 ^ 47 - 16) 3)
    ltac:(rewrite Erow, unsigned_lit_small by lia; split; [lia|];
          split; [change (2 ^ 3) with 8; exact HrowS8 | lia]).
  add_atom_win HS 103%nat (Z_to_bv 64 (11 - Z.of_nat (Datatypes.S i))) Ecnt.
  pin_by HS (19%bv : bv 5) (SOff 103 0)
    ltac:(rewrite !sv_denot_SOff0, Ecnt; ewpeel; rewrite E401; reflexivity).
  add_factA HS 103%nat (mkAF 1 11 0)
    ltac:(rewrite Ecnt, unsigned_lit_small by (clear - HiS; unfold CAT_N in HiS; lia);
          clear - HiS; unfold CAT_N in HiS; split; [lia|]; split; [rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]).
  clear E400 E401.
  ra_join_win HS ss_PL 280%nat pp_deads_PL_bv ltac:(idtac).
  pp_hand RL HS.
  split; [exact Hlv|]. split; [exact Hsne|]. split; [exact HiS|].
  split; [ewpeel; exact Etl|]. split; [ewpeel; exact Erow|]. split; [ewpeel; exact Ecnt|].
  intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne2]; [exact Hne | apply Hprev; clear - Hj Hne2; lia]. }
(* not taken: row i was row 10, so no row holds the token; 0x80d00 a3 = -1, `j 0x80d94`, and the count
   cell's shadow byte goes back to 0xf8 *)
hc_bool Hc ltac:(fun H => hc_off H 103%nat (11 - Z.of_nat i) (-1) Ecnt). hc_prop Hc.
rewrite Z.mod_small in Hc by lia.
assert (Hi10 : i = 10%nat) by (clear - Hi Hc; unfold CAT_N in Hi; lia).
assert (Hall : forall j, (j < CAT_N)%nat -> tok_bytes j <> pin_token s).
{ intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne2];
  [exact Hne | apply Hprev; clear - Hj Hne2 Hi10; unfold CAT_N in Hj; lia]. }
assert (Hres : pin_parse_res cat DP sa mo lb s = None)
  by exact (pp_res_norow cat DP sa mo lb s (pp_row_none s Hall)).
pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80d94.
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
rebaseE HS AG HEv. clear HEv.
(* the frame's 8 shadow bytes, writable for the store at 0x80d98 *)
pose proof (proj1 HJ) as HARy.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARy Hfin) as (_ & _ & _ & HFS2).
change (fs_frame_bytes 0 / 8) with 8 in HFS2. rewrite !EFA in HFS2.
pp_fs_rw HS E88 HFS2.
pl_run_sh HS HJ AG fpos F EFA 0x80d9c.
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
pp_fs_ro HS.
rebaseE HS AG HEv. clear HEv.
(* the result word of the refusal *)
add_atom_win HS 104%nat (Z_to_bv 64 (-1)) Erc.
pin_by HS (13%bv : bv 5) (SOff 104 0)
  ltac:(rewrite sv_denot_SOff0, Erc; cbn [sv_denot]; exact pp_w64_m1).
ra_join_win HS ss_P4 200%nat pp_deads_P4_bv ltac:(idtac).
pp_hand R4 HS.
split.
- rewrite Hres, pp_rc_none. ewpeel. exact Erc.
- intros row lab Hs2. rewrite Hres in Hs2. discriminate.
Qed.
End n.

(* ===================== 7. 0x80cc0: row i's check, its token, the two wrapper calls ===================== *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
(* the table is read-only image memory, so it misses the class-0 frame the function takes; the close
   discharges it by computation at the image's own table address *)
Hypothesis CATIMG : forall x, cat <= x < cat + CAT_BYTES -> in_img tfibsegs x.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B 0x41914.

(* 0x80cc0 the instrumented check of row i's first 8 bytes (its error path 0x80e68 is not reached),
   0x80cc8 s10 = TP i, 0x80cd0 the strlen wrapper on it, 0x80cd4 `bne a0,s9` -> ss_PN, else 0x80ce4 the
   strncmp wrapper on the spec string and the token, 0x80ce8 `beqz a0` -> ss_P3, else ss_PN. *)
Lemma pp_row : forall i,
pp_from B MT RLO RHI cat TP DP ss_P3 (INV_P3 B MT RLO RHI cat TP DP) ->
pp_from B MT RLO RHI cat TP DP ss_PN (INV_PN B MT RLO RHI cat TP DP i) ->
pp_from B MT RLO RHI cat TP DP ss_PL (INV_PL B MT RLO RHI cat TP DP i).
Proof.
intros i R3 RN. pp_prelude.
destruct HINV as (Hlv & Hsne & Hi & Etl & Erow & Ecnt & Hprev).
unfold PN_tl, PN_row, PN_cnt in Etl, Erow, Ecnt.
assert (HiZ : 0 <= Z.of_nat i <= 10) by (clear - Hi; unfold CAT_N in Hi; lia).
(* the spec string: its block, its bytes at entry, its window, and the out-cells that miss it [as in
   lib/A/PPgParse2.v pp_seg2, the same premises] *)
destruct (proj1 (pp_live_iff sa mo lb) Hlv) as (Hsa0 & Hmo0 & Hlb0).
destruct (Hstr Hsa0) as (HSTR & bq & mq & Hbq & Hbq0 & Hbq1).
pose proof HSTR as (HNs & _ & _ & _ & _ & _ & _ & _ & _ & HWs).
destruct (Hlive Hlv) as (Hmo8 & Hlb8 & Hmolb & Hinm & Hcm & Hfam & Hmo1 & Hmo2 & Hinl & Hcl & Hfal & Hlb1 & Hlb2
  & HAFm & HAFl & HOCw & HOCs).
assert (HEos : forall x, (pin_parse_live sa mo lb = true /\ pin_out_cell mo lb x) ->
  ~ (sa <= x <= sa + Z.of_nat (length s))) by (intros x [_ Hx]; exact (HOCs x Hx)).
pose proof (colon_idx_le s) as Hcle.
(* the table at the memory of the loop, from the contract's F-RO-LAW *)
edestruct (pl_ro_now B RLO RHI cat TP DP RELRO) as (HcatN & HcolN);
  [exact HROD | exact Hrolaw | exact HKE | exact HJ |].
pose proof HcatN as (Hc0 & Hc8 & Hc63 & Hcamr & Hcra & HrowsN).
destruct (HrowsN i Hi) as (HTPv & HDPv & HTPb & HDPb & HTPstr).
assert (HARO : aro_unowned tfibsegs B (aview tfibsegs (w_H WN) (ms_mem msN)))
  by exact (pl_aro_now B RLO RHI _ _ _ _ _ _ _ _ _ HROD HKE).
assert (Hrow8 : row_addr cat i mod 8 = 0) by (apply row_addr_mod8; exact Hc8).
assert (Hrowlo : 0 < row_addr cat i) by (apply row_addr_pos; exact Hc0).
assert (Hrowhi : row_addr cat i + 16 <= cat + CAT_BYTES) by exact (proj2 (pl_row_in cat i Hi)).
assert (Hrowge : cat <= row_addr cat i) by exact (proj1 (pl_row_in cat i Hi)).
assert (HrowI : TFIB_IMG_LO <= row_addr cat i /\ row_addr cat i + 8 <= TFIB_IMG_END).
{ split.
  - exact (proj1 (tfib_img_range _ (CATIMG (row_addr cat i) ltac:(clear - Hrowge Hrowhi; lia)))).
  - pose proof (tfib_img_range _ (CATIMG (row_addr cat i + 7) ltac:(clear - Hrowge Hrowhi; lia))) as Hx.
    clear - Hx; lia. }
unfold TFIB_IMG_LO, TFIB_IMG_END in HrowI.
assert (HrowL : row_addr cat i + 8 <= 0x7fff8000).
{ pose proof (tfib_segs_low _ (CATIMG (row_addr cat i + 7) ltac:(clear - Hrowge Hrowhi; lia))) as Hx.
  unfold kLowMemEnd in Hx. clear - Hx; lia. }
pose proof (pp_oc_frames_of_pre B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sa mo lb s
  cidm posm cidl posl HJ0 Hlive) as HOCF.
assert (HslC : alloc_ceiling <= spZ regs - T_parse_STK)
  by (change T_parse_STK with 8400; clear - Hceil Hslo HspLo; lia).
assert (HshC : spZ regs <= 2 ^ 64) by (clear - Hshi HspHi H47; lia).
assert (HlyF : ly_F lyN = ly_F lyc) by exact (pp_lyF B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  STK sp0 FP W0 mem0 md0 ((0, fpos) :: own) lyN SN WN (ms_mem msN) mdN k HJ0 HJ).
ppLOW HS AG E32 E32n.
(* row i's 8 bytes, as a read-only region, for `ld s10,0(s7)`; the table is image memory, so the region
   misses the class-0 frame, its shadow bytes and the caller's stack *)
add_atom_win HS 405%nat (Z_to_bv 64 (TP i)) E405.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv
  (YP09.mkRegion (Some 102%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 405 0))]) HS eq_refl) as HS3;
specialize (HS3 ltac:(
  unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
  ewpeel; rewrite Erow, unsigned_lit_small by (clear - Hrowlo Hrowhi Hcamr;
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hcamr; lia);
  split; [clear - Hrowlo; lia|];
  split; [clear - Hrowhi Hcamr; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hcamr; lia|];
  split; [intros oo Hoo; exfalso; clear - Hoo; lia|];
  apply Forall_cons; [| apply Forall_nil];
  apply (chunk_ok_val tfibsegs _ _ _ 0 8%N (SOff 405 0) (TP i));
  [ rewrite sv_denot_SOff0; ewpeel; exact E405
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HTPb; lia
  | cbn; lia
  | rewrite Z.add_0_r; exact HTPv ]));
specialize (HS3 ltac:(
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  evalE AG; repeat split; zone_lia));
clear HS; rename HS3 into HS; norm_ss HS end.
(* 0x80cc0 the shadow byte of row i's first granule is 0, so the `bnez` is not taken; 0x80cc8 s10 = TP i,
   0x80ccc a0 = s10, 0x80cd0 the call of the strlen wrapper *)
pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x41908.
{ lazymatch goal with |- range_addressable _ (U ?Ev _) _ _ =>
  rewrite (U_atom Ev 102%nat (row_addr cat i) ltac:(ewpeel; exact Erow)
    ltac:(clear - Hrowlo Hrowhi Hcamr; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hcamr; lia));
  rewrite (U_atom Ev 32%nat SB ltac:(ewpeel; exact E32n) ltac:(unfold SB; lia)) end.
  rewrite <- (aview_rd_of tfibsegs), SB_SHADOW_OFF.
  eapply range_addressable_sub; [exact Hcra | clear - Hrowge; lia | clear - Hrowhi; lia]. }
(* the run moved the memory: the kept fact and the read-only facts move with it *)
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
rebaseE HS AG HEv. clear HEv. ppLOW HS AG E32 E32n.
clear HcatN HcolN Hc0 Hc8 Hc63 Hcamr Hcra HrowsN HTPv HDPv HTPb HDPb HTPstr HARO.
edestruct (pl_ro_now B RLO RHI cat TP DP RELRO) as (HcatN & HcolN);
  [exact HROD | exact Hrolaw | exact HKE | exact HJ |].
pose proof HcatN as (Hc0 & Hc8 & Hc63 & Hcamr & Hcra & HrowsN).
destruct (HrowsN i Hi) as (HTPv & HDPv & HTPb & HDPb & HTPstr).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HARO : aro_unowned tfibsegs B (aview tfibsegs (w_H WN) (ms_mem msX)))
  by exact (pl_aro_now B RLO RHI _ _ _ _ _ _ _ _ _ HROD HKE) end.
(* the call itself: a0 = TP i, ra = 0x80cd4, sp = sp1 *)
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _ & _).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (10%bv : bv 5) Ra0.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (EspX : spZ (ms_regs msX) = sp0 + (sp1 - sp0));
[ unfold spZ; rewrite Rsp, E70;
  rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hshi H47 HspLo HspHi C1; lia); lia | ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HwinT : forall a, TP i <= a <= TP i + Z.of_nat (length (tok_bytes i)) ->
  ~ (spZ (ms_regs msX) - 2 * ESTACK <= a < spZ (ms_regs msX))) end.
{ rewrite EspX.
  apply (pin_off_window (spZ regs - T_parse_STK) (spZ regs)).
  - change T_parse_STK with 8400. clear - Hsp1 Hes; lia.
  - clear - Hsp1; lia.
  - intros a Ha. exact (proj2 Hcatst i a Hi Ha). }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SRr_bind;
[ eapply (aj_strlen_at tfibsegs B LAWS tfib_segs_low 0x41908 ASTRLEN WN (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyN SN mdX k (TP i) (tok_bytes i) (sp1 - sp0) _ HJ);
  [ rewrite Ra0; exact E405
  | exact EspX
  | rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity
  | clear - Hsp1 HspHi; lia
  | clear - Hsp1 Hes HspLo HspHi; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
  | exact Rra
  | apply ret_ok_even; vm_compute; reflexivity
  | apply (pp_awrap_of_ro tfibsegs WN (ms_mem msX) (ms_regs msX) (TP i) (tok_bytes i) HTPstr);
    [ intros Hin; exact (tokens_no_nul i _ Hi Hin eq_refl) | exact HwinT ]
  | exact HARO ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HIO2 & HP2 & Hlen2 & Hfr2 & Hpres2).
assert (HIOx : same_io mdc md2)
  by first [ exact (same_io_trans _ _ _ HIO HIO2)
           | eapply same_io_trans; [eapply same_io_trans; [exact HIO | apply same_io_with_vm_backing] | exact HIO2] ].
clear HIO HIO2. rename HIOx into HIO.
replace (sp0 + (sp1 - sp0)) with sp1 in Hfr2 by lia.
(* the caller's memory after the wrapper: only its window [sp1 - 2 * ESTACK, sp1) changed *)
pl_kept_call HJ2 Hfr2 Hpres2 (fun a => sp1 - 2 * ESTACK <= a < sp1) HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
clear HJ. rename HJ2 into HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT2 & _).
pose proof (proj1 HJ) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (_ & _ & HFB2 & _).
change (fs_frame_bytes 0) with 64 in HFB2. rewrite !EFA in HFB2. fold F in HFB2.
(* the re-seat: the five regions are kept (the row's 8 bytes are image memory, the rest is the frame, its
   shadow and the caller's stack above the callee's window); the clobbered registers get the junk atoms 410.. *)
pl_reseat HS 410%nat HJ HP2 [0; 1; 2; 3; 4]%nat AG
  ltac:(idtac; ppKEPTO Hfr2 AG ltac:(fail)
    ltac:(idtac; first [ apply HpresT2; lia
                       | match goal with |- apresent _ _ ?x => apply (proj1 (HFB2 x ltac:(lia))) end ])) HE2.
lazymatch type of HE2 with ?Ev = havoc ?Eo _ _ =>
  assert (E414 : ew Ev 414 = Z_to_bv 64 (Z.of_nat (length (tok_bytes i))))
  by (rewrite HE2; change 414%nat with (410 + 4)%nat; rewrite (ew_havoc_new Eo 410 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map CLOB]; rewrite Hlen2; reflexivity) end.
clear HE2 Hlen2 Rra Rsp Rgp Rtp Ra0 EspX HwinT HFB2 HpresT2 HAR2 Hfr2 Hpres2 HP2.
(* the spec string at this memory, and the lengths the branch compares *)
pose proof (pp_spec_now tfibsegs B LAWS lyc Sc W memc lyN SN WN mem2 _ _ _ _ regs T_parse_STK sa s bq mq
  (proj1 HJ) HPERM HKE HEos Hbq Hbq0 Hbq1 HSTR) as HROs.
pose proof HROs as (_ & _ & HlenS & _).
pose proof HTPstr as (_ & _ & HlenT & _).
(* 0x80cd4 `bne a0,s9`: the token's length against toklen *)
pp_br HS Hc.
{ (* taken: the lengths differ, so the token is not the spec's; on to the next row *)
  hc_bool Hc ltac:(fun H => hc_off H 414%nat (Z.of_nat (length (tok_bytes i))) 0 E414;
                            hc_off H 100%nat (Z.of_nat (colon_idx s)) 0 Etl).
  hc_prop Hc.
  rewrite ?Z.add_0_r in Hc. rewrite !Z.mod_small in Hc by lia.
  assert (Hne : tok_bytes i <> pin_token s)
    by (apply (pp_strlen_ne i s (colon_idx s) eq_refl); clear - Hc; lia).
  pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80cec.
  pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
    HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
  rebaseE HS AG HEv. clear HEv.
  ra_join_win HS ss_PN 260%nat pp_deads_PL_bv ltac:(idtac).
  pp_hand RN HS.
  split; [|exact Hne].
  split; [exact Hlv|]. split; [exact Hsne|]. split; [exact Hi|].
  split; [ewpeel; exact Etl|]. split; [ewpeel; exact Erow|]. split; [ewpeel; exact Ecnt|].
  exact Hprev. }
(* not taken: the lengths agree *)
hc_bool Hc ltac:(fun H => hc_off H 414%nat (Z.of_nat (length (tok_bytes i))) 0 E414;
                          hc_off H 100%nat (Z.of_nat (colon_idx s)) 0 Etl).
hc_prop Hc.
rewrite ?Z.add_0_r in Hc. rewrite !Z.mod_small in Hc by lia.
assert (HlenEq : length (tok_bytes i) = colon_idx s) by (clear - Hc; lia).
(* 0x80cd4 (the `bne` falls through) .. 0x80ce4: a0 = sa, a1 = s10 = TP i, a2 = s9 = toklen, the call of the
   strncmp wrapper *)
pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x41914.
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
rebaseE HS AG HEv. clear HEv. ppLOW HS AG E32 E32n.
(* the token and the spec string at the memory of the call *)
clear HcatN HcolN Hc0 Hc8 Hc63 Hcamr Hcra HrowsN HTPv HDPv HTPb HDPb HTPstr HARO HROs.
edestruct (pl_ro_now B RLO RHI cat TP DP RELRO) as (HcatN & HcolN);
  [exact HROD | exact Hrolaw | exact HKE | exact HJ |].
pose proof HcatN as (Hc0 & Hc8 & Hc63 & Hcamr & Hcra & HrowsN).
destruct (HrowsN i Hi) as (HTPv & HDPv & HTPb & HDPb & HTPstr).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HARO : aro_unowned tfibsegs B (aview tfibsegs (w_H WN) (ms_mem msX)))
  by exact (pl_aro_now B RLO RHI _ _ _ _ _ _ _ _ _ HROD HKE);
pose proof (pp_spec_now tfibsegs B LAWS lyc Sc W memc lyN SN WN (ms_mem msX) _ _ _ _ regs T_parse_STK sa s bq mq
  (proj1 HJ) HPERM HKE HEos Hbq Hbq0 Hbq1 HSTR) as HROs end.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (EspX : spZ (ms_regs msX) = sp0 + (sp1 - sp0));
[ unfold spZ; rewrite Rsp, E70;
  rewrite unsigned_lit_small by (clear - Hsp1 Hceil Hslo Hshi H47 HspLo HspHi C1; lia); lia | ] end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (HwinS : forall a, sa <= a <= sa + Z.of_nat (length s) ->
  ~ (spZ (ms_regs msX) - 2 * ESTACK <= a < spZ (ms_regs msX)));
[ rewrite EspX; intros a Ha Hw; apply (HWs a Ha); change T_parse_STK with 8400; clear - Hw Hsp1 Hes; lia | ];
assert (HwinT : forall a, TP i <= a <= TP i + pin_tokn i ->
  ~ (spZ (ms_regs msX) - 2 * ESTACK <= a < spZ (ms_regs msX)));
[ rewrite EspX; intros a Ha Hw; apply (proj2 Hcatst i a Hi Ha); change T_parse_STK with 8400;
  clear - Hw Hsp1 Hes; lia | ];
destruct (pin_strncmp_site tfibsegs TP WN (ms_mem msX) (ms_regs msX) sa s i HROs HNs HwinS Hi HTPstr HwinT HlenEq)
  as (HawS & HawT & HamS2 & HamT2 & Hn32 & _) end.
destruct (pp_strncmp_tok i s (colon_idx s) Hi HNs eq_refl ltac:(rewrite HlenEq; reflexivity)) as (d & Hd & Hdiff).
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SRr_bind;
[ eapply (aj_strncmp_at tfibsegs B LAWS tfib_segs_low 0x41914 ASTRNCMP WN (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyN SN mdX k sa (TP i) (Z.of_nat (colon_idx s)) s (tok_bytes i) d
    (sp1 - sp0) _ HJ);
  [ rewrite Ra0, (AG 10%nat) by lia; exact E10
  | rewrite Ra1; exact E405
  | rewrite Ra2; exact Etl
  | exact Hn32
  | exact EspX
  | rewrite Zminus_mod, Hsp1al16, Hsp0al; reflexivity
  | clear - Hsp1 HspHi; lia
  | clear - Hsp1 Hes HspLo HspHi; lia
  | rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp
  | rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp
  | exact Rra
  | apply ret_ok_even; vm_compute; reflexivity
  | exact HawS | exact HawT | exact HamS2 | exact HamT2 | exact Hd | exact HARO ]
| ] end.
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HIO3 & HP3 & (v & Ha03 & Hv0) & Hfr3 & Hpres3).
assert (HIOx : same_io mdc md3)
  by first [ exact (same_io_trans _ _ _ HIO HIO3)
           | eapply same_io_trans; [eapply same_io_trans; [exact HIO | apply same_io_with_vm_backing] | exact HIO3] ].
clear HIO HIO3. rename HIOx into HIO.
replace (sp0 + (sp1 - sp0)) with sp1 in Hfr3 by lia.
pl_kept_call HJ3 Hfr3 Hpres3 (fun a => sp1 - 2 * ESTACK <= a < sp1) HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
clear HJ. rename HJ3 into HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT3 & _).
pose proof (proj1 HJ) as HAR3.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 Hfin) as (_ & _ & HFB3 & _).
change (fs_frame_bytes 0) with 64 in HFB3. rewrite !EFA in HFB3. fold F in HFB3.
pl_reseat HS 430%nat HJ HP3 [0; 1; 2; 3; 4]%nat AG
  ltac:(idtac; ppKEPTO Hfr3 AG ltac:(fail)
    ltac:(idtac; first [ apply HpresT3; lia
                       | match goal with |- apresent _ _ ?x => apply (proj1 (HFB3 x ltac:(lia))) end ])) HE3.
lazymatch type of HE3 with ?Ev = havoc ?Eo _ _ =>
  assert (E434 : ew Ev 434 = Z_to_bv 64 (bv_unsigned v))
  by (rewrite HE3; change 434%nat with (430 + 4)%nat; rewrite (ew_havoc_new Eo 430 _ 4 (Z_to_bv 64 0)) by (cbn; lia);
      cbn [nth map CLOB]; rewrite Ha03, Z_to_bv_bv_unsigned; reflexivity) end.
pose proof (bv_unsigned_in_range 64 v) as Hvr. change (bv_modulus 64) with (2 ^ 64) in Hvr.
clear HE3 Ha03 Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 EspX HwinS HwinT HFB3 HpresT3 HAR3 Hfr3 Hpres3 HP3.
(* 0x80ce8 `beqz a0`: the strncmp result against 0 *)
pp_br HS Hc2.
{ (* taken: the token is the spec's, and no earlier row's is: row i is the first match *)
  hc_bool Hc2 ltac:(fun H => hc_off H 434%nat (bv_unsigned v) 0 E434).
  hc_prop Hc2.
  rewrite ?Z.add_0_r in Hc2. rewrite ?Z.mod_small in Hc2 by lia.
  assert (Hd0 : d = 0).
  { apply (proj1 Hv0). rewrite <- (Z_to_bv_bv_unsigned _ v). unfold w64. f_equal. clear - Hc2 Hvr. lia. }
  assert (Htok : tok_bytes i = pin_token s) by exact (proj1 Hdiff Hd0).
  pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80d08.
  pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
    HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
  rebaseE HS AG HEv. clear HEv.
  ra_join_win HS ss_P3 240%nat pp_deads_P3_bv ltac:(idtac).
  pp_hand R3 HS.
  exists i. split; [exact Hlv|]. split; [exact Hsne|]. split; [exact Hi|].
  split; [ewpeel; exact Etl|]. split; [ewpeel; exact Erow|]. split; [exact Htok|].
  exact (pl_row_found s i Hi Htok Hprev). }
(* not taken: the token is not the spec's; on to the next row *)
hc_bool Hc2 ltac:(fun H => hc_off H 434%nat (bv_unsigned v) 0 E434).
hc_prop Hc2.
rewrite ?Z.add_0_r in Hc2. rewrite ?Z.mod_small in Hc2 by lia.
assert (Hne : tok_bytes i <> pin_token s).
{ intros Htok. apply Hc2. apply (proj2 Hdiff) in Htok. apply (proj2 Hv0) in Htok.
  rewrite Htok. reflexivity. }
pp_run_to HS HJ AG fpos F EFA ltac:(fail) 0x80cec.
pl_kept AG (fun a => (spZ regs - T_parse_STK <= a < spZ regs) \/ pp_nf F FL a)
  HAR0 Hfrs HPERM HlyF FFL HslC HshC HOCF.
rebaseE HS AG HEv. clear HEv.
ra_join_win HS ss_PN 260%nat pp_deads_PL_bv ltac:(idtac).
pp_hand RN HS.
split; [|exact Hne].
split; [exact Hlv|]. split; [exact Hsne|]. split; [exact Hi|].
split; [ewpeel; exact Etl|]. split; [ewpeel; exact Erow|]. split; [ewpeel; exact Ecnt|].
exact Hprev.
Qed.
End w.

(* ===================== 8. the row loop: 0x80cc0 at row i -> 0x80d08 | 0x80d9c ===================== *)
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B 0x41914.
Variables RLO RHI cat : Z.
Variables TP DP : nat -> Z.
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Hypothesis CATIMG : forall x, cat <= x < cat + CAT_BYTES -> in_img tfibsegs x.
Lemma pp_seg2L : PP_seg2L B MT RLO RHI cat TP DP.
Proof.
unfold PP_seg2L. intros R3 R4.
apply (pp_loop B MT RLO RHI cat TP DP).
- intros i. eapply pp_row; eassumption.
- intros i. eapply pp_next; eassumption.
- exact R3.
- exact R4.
Qed.
End f.
