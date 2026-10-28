(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c8 X1bj X1cc X1bu X1bq X1bs X1c2 X1bn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require X1bk X1c5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1rd X1oc X1ri X1rl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1fd X1fc X1gi X1en X1fl X1ei. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1eh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fo X1ea X1jh. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1jg. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1jj X1fr.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1fq.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cb.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.

Module F_printf_core_cvs.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation strnlen_callq := (X1fq.strnlen_callq q gp tp lo LO GLO QHI).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation S_TAIL := (X1fq.S_TAIL (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_S := (X1fq.S_CV_S (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_TAIL : S_TAIL.

Lemma L_CV_S : S_CV_S.
Proof using BS0 GLO HA HAP HS_TAIL HVA LO QHI SEP_B SEP_F SFR VAHI.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p fl10 xp P s slack pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP STR SRNG SPAD P0 SD1 SD2 SD3 E10.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app, zb_length in SB. cbn [length] in SB.
assert (LSB : Z.of_nat (length (zb s ++ Z_to_bv 8 0 :: slack)) = (Z.of_nat (length s) + 1 + Z.of_nat (length slack))%Z)
by (rewrite length_app, zb_length; cbn [length]; lia).
pose proof (zb_nonul s SRNG) as NONUL. pose proof (zb_length s) as LZS.
pose proof (land_bound' fl 18446744073709486079 ltac:(lia) ltac:(lia)) as FLB. rewrite (nzmask_eq fl) in FLB by lia.
assert (BRNG : forall n, Forall (fun c0 => 0 <= c0 < 256)%Z (firstn n s)).
{ intros n. rewrite <- (skipn_O s). apply Forall_sub. eapply Forall_impl; [|exact SRNG]. cbv beta. intros. lia. }
stmt (HS_TAIL fuel HH) as NX.
set (len := Z.of_nat (length s)) in *.
unfold ZERO_PAD.
ienter.
zs. zs. brf K0; [|exfalso; lia].
destruct XP as [[-> ->] | [-> Hp]].
-
cbn [Z.b2z]. change ((-1) <? 0)%Z with true. cbn [andb].
destruct (Z.leb_spec0 2147483647 len) as [BIG|SMALL]; [ileave; apply implM_unr_l|].
rewrite ?ift, ?iff.
zs. zs. if_lit. zs. zs. zs.
callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack) (n := 2147483647%Z);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; (clear - LZS SB LU LZB SPAD len slack s P slots fmt; lia)] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (clear - K0 LZS SB SD1 P0 slack s P lo q; lia) | (clear - K0 LZS SB P0 SPAD slack s P; lia) | lia ]).
rewrite (strnlen_res_cstr 0) by exact NONUL. rewrite zb_length. fold len. replace (Z.min len 2147483647) with len by lia.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR1 end.
zs. zs. if_lit.
assert (NTH : nth_error (zb s ++ Z_to_bv 8 0 :: slack) (Z.to_nat len) = Some (Z_to_bv 8 0)).
{ rewrite nth_error_app2 by (rewrite zb_length; lia). rewrite zb_length. replace (Z.to_nat len - length s)%nat with 0%nat by lia. reflexivity. }
pose proof (u8ro_read rsegs _ P (zb s ++ Z_to_bv 8 0 :: slack) len (Z_to_bv 8 0) _ STR1 NTH ltac:(lia) eq_refl) as RD.
zs. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. zs. if_lit. zs. zs. zs. zs. zs. zs. zs.
match goal with H : bytes_at _ ?mm P _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at rsegs mm P (zb s)) end.
{ pose proof STR2 as STR3. apply bytes_at_app in STR3. exact (proj1 STR3). }
rewrite (@firstn_all2 Z (Z.to_nat len) s) by (unfold len; lia).
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := len) (prefix := []) (body := s) (BA := P) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | eapply Forall_impl; [|exact SRNG]; cbv beta; intros; (clear - H a; lia)
| unfold body_loc; zl | zl | unfold INT_MAX; zl
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | (clear - FLB Hfl fl; lia) | unfold INT_MAX; (clear - Hw w; lia) | unfold INT_MAX; (clear - SMALL K0 LZS SB P0 slack s P; lia) | unfold INT_MAX; (clear - Hc c; lia) ].
match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
-
replace (p <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb Z.b2z]. rewrite ?ift, ?iff.
zs. zs. brf K1; [ | zs ].

all: zs; zs.
all: callx (eapply strnlen_callq with (buf := zb s ++ Z_to_bv 8 0 :: slack);
[ exact ST | exact STR | apply memchr_ok_cstr; [exact NONUL | rewrite zb_length; unfold zlength in *; (clear - LZS SB LU LZB SPAD len slack s P slots fmt; lia)] | exact MI
| rewrite length_app, zb_length; cbn [length]; unfold zlength in *; (clear - K0 LZS SB SD1 P0 slack s P lo q; lia) | (clear - K0 LZS SB P0 SPAD slack s P; lia) | (clear - K1 Hp p; lia) ]).
all: rewrite (strnlen_res_cstr 0) by exact NONUL; rewrite zb_length; fold len.
all: zs; zs; br K2; zs; zs; zs; zs; zs; zs; zs.
all: match goal with H : bytes_at _ ?mm ?PP (zb _ ++ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STR2 end.
all: lazymatch type of STR2 with bytes_at _ ?mm _ _ => assert (SUB : bytes_at rsegs mm P (zb (firstn (Z.to_nat (Z.min len p)) s)))
by (pose proof STR2 as STR3; rewrite <- (firstn_skipn (Z.to_nat (Z.min len p)) s) in STR3; rewrite zb_app, <- app_assoc in STR3; apply bytes_at_app in STR3; exact (proj1 STR3)) end.
all: assert (LF : zlength (firstn (Z.to_nat (Z.min len p)) s) = Z.min len p) by (unfold zlength; rewrite length_firstn; lia).
all: jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := Z.land fl (Z.lnot 65536)) (w := w) (p := Z.min len p) (prefix := []) (body := firstn (Z.to_nat (Z.min len p)) s) (BA := P) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | | exact APC | (clear - Hk k; lia) | exact AOK | exact FPC | exact FRM | exact FOK
| exact SUB | apply BRNG
| unfold body_loc; rewrite LF; (clear - K0 LZS SB SD3 SD2 SD1 P0 SPAD slack s P p lo q BS B Fp; lia) | rewrite LF; (clear - K0 LZS SB P0 SPAD slack s P p; lia) | rewrite LF; unfold INT_MAX; (clear - K1 K0 LZS SB P0 slack s P p Hp; lia)
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | (clear - FLB Hfl fl; lia) | unfold INT_MAX; (clear - Hw w; lia) | unfold INT_MAX; (clear - K1 K0 LZS SB P0 Hp slack s P p; lia) | unfold INT_MAX; (clear - Hc c; lia) ].
all: match goal with H : SINK ?mm _ |- SINK ?mm _ => exact H end.
Qed.
End PrintfCore.
End F_printf_core_cvs.

Module F_printf_core_pro.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PRO := (X1fq.S_PRO Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_PRO : S_PRO.
Proof using BS0 GLO HA HAP HVA LO QHI SEP_F.
intros x5 x6 x7 x15 x16 x17 x28 x29 x30 x31 f Q _ ST0 MI0 BY0 VAA0 SSP0 Hf CONT.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO. unfold zlength in *.
destruct SSP0 as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. fix_rsegs.
pose proof (zb_length fmt) as LZB. pose proof (u64s_length slots) as LU. unfold va_area in VAA0.
pose proof (munch_refl [(q + -544, q)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
pose proof ST0 as ST.
carve_frame 544%nat ST.
do 43 zs.

lazymatch type of FR with rw_cells _ _ _ (CB 40 ?ja :: _) => set (jA := ja) in FR; clearbody jA end.
lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 320 ?jb :: _) => set (jB := jb) in FR; clearbody jB end.
apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [LOWa FRhi]. cbn [cells_size csize Nat.add app] in FRhi.
replace (q + -544 + Z.of_nat 432)%Z with (q + -112)%Z in FRhi by lia.
apply (rw_cells_split_CB rsegs _ _ [_;_;_;_;_;_;_;_;_;_] 320 _ [] [16; 24; 24; 256]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB rsegs _ _ [] 40 _ _ [8; 8; 8; 8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
apply (rw_cells_split_CB rsegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] 16 _ _ [8; 8]%nat) in LOWa; [ | cbn; lia ].
cbn [mk_CB_cells app] in LOWa.
do 7 c8ify LOWa.
apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in LOWa. destruct LOWa as [LOW DP]. cbn [cells_size csize Nat.add app] in DP.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in DP. destruct DP as [DIG PAD]. cbn [cells_size csize Nat.add app] in PAD.
replace (q + -544 + Z.of_nat 152)%Z with (q + -392)%Z in DIG by lia.
replace (q + -544 + Z.of_nat 152 + Z.of_nat 24)%Z with (q + -368)%Z in PAD by lia.
eapply CONT; [ | exact MU | exact LOW | exact DIG | exact PAD ].
unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area.
split; [assumption|]. split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|]. split; [exact WM|].
split; [exact FRhi|]. split; [exact ST|]. split; [exact BY0|]. split; [exact VAA0|]. split; [exact SSP1|exact SSP2].
Qed.
End PrintfCore.
End F_printf_core_pro.

Module F_printf_core_dir.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_FLAGS := (X1fq.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_WIDTH := (X1fq.S_WIDTH Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_PREC := (X1fq.S_PREC Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_STATE := (X1fq.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_DIR := (X1fq.S_DIR Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation sfx := (sfx fmt).
Notation qq := (q + -544)%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_FLAGS : S_FLAGS.
Hypothesis HS_WIDTH : S_WIDTH.
Hypothesis HS_PREC : S_PREC.
Hypothesis HS_STATE : S_STATE.

Lemma L_DIR : S_DIR.
Proof using HF HS_FLAGS HS_PREC HS_STATE HS_WIDTH.
intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q i d rest pfx s2s za pl plp alo ahi j128 _
FI LOW Hi Hi1 PD HK.
pose proof FI as FI'. dest_finv FI. pose proof LOW as LOW'. unfold lo_cells, ssp_guard in LOW.
pose proof (parse_dir_shape _ _ _ PD) as (POSN & SH).
destruct (parse_flags (sfx (i + 1)) 0) as [fl s1] eqn:PF.
first [ sf_destruct 11%nat SH as Efl c1' s1b Es1 N42 s2 G c2 s2b Es2 PX | sf_fb; destruct SH as (Efl & c1' & s1b & Es1 & N42 & s2 & G & c2 & s2b & Es2 & PX) ].

destruct (parse_flags_suffix _ _ _ _ PF) as (n1 & Hs1 & Hn1). rewrite sfx_skipn in Hs1 by lia. set (k1 := (i + 1 + Z.of_nat n1)%Z) in Hs1.
rewrite Hs1 in Es1. destruct (sfx_cons_inv fmt k1 c1' s1b ltac:(lia) Es1) as (Hk1 & Ec1' & Es1b).
destruct (getint_suffix _ _ _ _ G) as (n2 & Hs2 & Hn2). rewrite Hs1, sfx_skipn in Hs2 by lia. set (k2 := (k1 + Z.of_nat n2)%Z) in Hs2.
rewrite Hs2 in Es2. destruct (sfx_cons_inv fmt k2 c2 s2b ltac:(lia) Es2) as (Hk2 & Ec2 & Es2b).
assert (Hi1' : (i + 1 < zlength fmt)%Z) by zl.
rewrite (sfx_cons fmt (i + 1)) in POSN, PF by zl.

assert (POSTFLAGS : forall (t0 t1 a3 a4 a5 a6 a7 : word),
evt rsegs Q
(MS (mkR x1 SPv gp tp t0 t1 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt k1)) (Z_to_bv 64 (A + k1)) a3 a4 a5 a6 a7
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 (Z_to_bv 64 fl) x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x35574) fc None m (seg_rom rsegs))).
{ intros t0 t1 a3 a4 a5 a6 a7.
pose proof (parse_flags_range (sfx (i + 1)) 0 ltac:(lia)) as FLR. rewrite (sfx_cons fmt (i + 1)), PF in FLR by zl. cbn [fst] in FLR.
stmt HS_WIDTH as NXW. jump (eapply NXW with (k1 := k1) (w := d_w d) (s2 := s2); [exact FI' | exact LOW' | lia | rewrite <- Hs1; exact G | rewrite Hs2, Es2; discriminate | ]).
intros k2' t0' t1' a1' a3' a4' a5' a6' a7' Hk2' Hs2' Hnd Hw.
assert (k2' = k2).
{ pose proof (sfx_length fmt k2 ltac:(zl)) as L1. pose proof (sfx_length fmt k2' ltac:(zl)) as L2. rewrite <- Hs2', Hs2 in L2. lia. }
subst k2'.
stmt HS_PREC as NXP. jump (eapply NXP with (k2 := k2) (p := d_p d) (xp := d_xp d) (k3 := (if d_xp d then k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 else k2)%Z);
[exact FI' | exact LOW' | lia | | ]).
{ destruct PX as [(N46 & Hp & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- left. rewrite <- Ec2, Hxp. repeat split; try assumption; reflexivity.
- right. rewrite Hxp. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK. split; [congruence|]. split; [reflexivity|]. split; [zl|]. split; [rewrite <- Ec3; exact N42q|].
split; [rewrite <- Es2b, <- Hs3; exact G2 | zl]. }
intros a1q a3q a4q Hp.
destruct PX as [(N46 & Hpq & Hxp & Ht & Hrest & CT) | (E46 & Hxp & c3 & s3b & Es2bq & N42q & s3 & G2 & Es3 & CT)].
- rewrite Hxp. cbn [Z.b2z].
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := k2) (ty := d_ty d); [exact FI' | zl | rewrite <- Ec2; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1)%Z); [zl | rewrite Hrest, Es2b; reflexivity | replace (k2 + 1 - 1)%Z with k2 by lia; rewrite <- Ec2, Ht; reflexivity | lia | lia | lia]).
- rewrite Hxp. cbn [Z.b2z]. rewrite Es2b in Es2bq. destruct (sfx_cons_inv fmt (k2 + 1) c3 s3b ltac:(lia) Es2bq) as (Hk21 & Ec3 & Es3b).
destruct (getint_suffix _ _ _ _ G2) as (n3 & Hs3 & Hn3). rewrite Es2b, sfx_skipn in Hs3 by lia.
rewrite Hs3 in Es3.
assert (Hk30 : (0 <= k2 + 1 + Z.of_nat n3)%Z) by (subst k1 k2; lia).
destruct (sfx_cons_inv fmt (k2 + 1 + Z.of_nat n3) (d_t d) rest Hk30 Es3) as (Hk3 & Et & Erest).
assert (EK : (k2 + 1 + Z.of_nat (length s2b) - Z.of_nat (length rest) - 1 = k2 + 1 + Z.of_nat n3)%Z).
{ rewrite Es2b, Erest. pose proof (sfx_length fmt (k2 + 1) ltac:(zl)). pose proof (sfx_length fmt (k2 + 1 + Z.of_nat n3 + 1) ltac:(zl)). unfold zlength in *. lia. }
rewrite EK.
stmt HS_STATE as NXS. jump (eapply NXS with (k3 := (k2 + 1 + Z.of_nat n3)%Z) (ty := d_ty d); [exact FI' | zl | rewrite <- Et; exact CT | ]).
intros a2q a3q2. rewrite Hxp in HK. cbn [Z.b2z] in HK.
jump (apply (HK (k2 + 1 + Z.of_nat n3 + 1)%Z); [zl | exact Erest | replace (k2 + 1 + Z.of_nat n3 + 1 - 1)%Z with (k2 + 1 + Z.of_nat n3)%Z by lia; symmetry; exact Et | lia | lia | lia]). }

assert (FL34 : forall (a3 a4 a5 : word), evt rsegs Q
(MS (mkR x1 SPv gp tp (Z_to_bv 64 75913) x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (-1)) (Z_to_bv 64 (znth fmt (i + 1))) (Z_to_bv 64 (A + i + 1)) a3 a4 a5 (Z_to_bv 64 1) x17
x18 x19 x20 (Z_to_bv 64 (A + i)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x354e4) fc None m (seg_rom rsegs))).
{ intros a3q a4q a5q. pose proof (fmt_rng (i + 1) ltac:(zl)) as RG.

assert (NOFLAG : flag_bit (znth fmt (i + 1)) = None -> fl = 0%Z /\ k1 = (i + 1)%Z).
{ intros NF. rewrite (parse_flags_cons_none _ _ _ NF) in PF. injection PF as Efl0 Es1q. split; [congruence|].
pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt (i + 1) ltac:(zl)) as L2.
rewrite (sfx_cons fmt (i + 1)) in L2 by zl. rewrite Es1q, Hs1 in L2. lia. }
zs. zs. zs. brf K2.
-
assert (NF : flag_bit (znth fmt (i + 1)) = None).
{ destruct (flag_bit (znth fmt (i + 1))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (i + 1)) ltac:(congruence)) as R. rewrite land_M64_id in K2 by lia. lia. }
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. zs. brf K3. { exfalso. apply N42. rewrite Ec1', Ek1. exact K3. }
jump (apply POSTFLAGS).
- assert (Hc : (32 <= znth fmt (i + 1) < 64)%Z) by (apply (proj1 (sp_test _ RG)); lia).
rewrite (land_M64_id (znth fmt (i + 1) + -32)) in * by lia.
zs. zs. zs. zs. zs. brf K3.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
assert (NF : flag_bit (znth fmt (i + 1)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
destruct (NOFLAG NF) as [Efl0 Ek1].
zs. zs. brf K4; [ jump (apply POSTFLAGS) | exfalso; apply N42; rewrite Ec1', Ek1; exact K4 ].
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (i + 1) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (i + 1))) in K3.
destruct (flag_bit (znth fmt (i + 1))) as [b|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb].
rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
zs.
stmt HS_FLAGS as NXF. jump (eapply NXF with (p := (i + 1)%Z) (k := 1%Z) (fl := 0%Z) (b := b) (FL := fl) (s1 := s1);
[exact FI' | lia | lia | zl | rewrite unsigned_lit_land; exact Hfw | lia | lia | rewrite Z.lor_0_l; exact PF | rewrite Hs1, Es1; discriminate | ]).
intros k' c' a3' a4' a5' Hk' Hs1' Hc' HN HFL.
assert (Ek1 : k' = k1).
{ pose proof (sfx_length fmt k1 ltac:(zl)) as L1. pose proof (sfx_length fmt k' ltac:(zl)) as L2. rewrite <- Hs1', Hs1 in L2. lia. }
subst k'. subst c'. pose proof (fmt_rng k1 ltac:(zl)) as RGk.
zs. zs. brf K4; [ | exfalso; apply N42; rewrite Ec1'; exact K4 ].
jump (apply POSTFLAGS). }

rd_fmt (i + 1)%Z. zs. fix_u8 (i + 1)%Z. zs. zs. zs. zs. zs. brf K.
-   zs. zs. apply FL34.
- assert (DG : is_digit (znth fmt (i + 1)) = true) by (apply (proj1 (digit_test _ RG)); lia).
assert (Hi2 : (i + 2 < zlength fmt)%Z).
{ destruct (Z.lt_ge_cases (i + 2) (zlength fmt)); [assumption|]. exfalso.
rewrite (sfx_nil fmt (i + 1 + 1)) in POSN by lia. rewrite DG in POSN. discriminate. }
replace (i + 1 + 1)%Z with (i + 2)%Z in POSN by lia.
rewrite (sfx_cons fmt (i + 2)) in POSN by zl. rewrite DG in POSN. cbn [andb] in POSN. apply Z.eqb_neq in POSN.
rd_fmt (i + 2)%Z. zs. fix_u8 (i + 2)%Z. zs. zs. zs. zs. br K1. apply FL34.
Qed.
End PrintfCore.
End F_printf_core_dir.

Module F_printf_core_t3.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_postq := (X1fq.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T4 := (X1fq.S_T4 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T3 := (X1fq.S_T3 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_T4 : S_T4.

Lemma L_T3 : S_T3.
Proof using BS0 GLO HA HAP HOUT HS_T4 HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
pose proof TI as TI'. dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad at 1. unfold LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 65536) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+ rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ exact TI' | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; (clear - K3 N256 n4 LP LB LU LZB body prefix pl pq wq w slots fmt; lia)].
zs. zs.
apply (rw_cells_split_CB rsegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | lia | (clear - N256 K2 LP Hwq body prefix pl pq wq w; lia)]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 48 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; lia].
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. (clear - K4 K2 LP LB LU LZB Hn n4 body prefix pl n pq wq w BS0 HAP SEP_B SEP_F GLO LO slots VA AP fmt lo q BS B Fp; lia). }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells rsegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt (HS_T4 fuel HH) as NX4.
jumpM (eapply NX4 with (k := k) (i4 := i4) (c := c) (w := w) (wq := wq) (pq := pq) (args := args) (PFXA := PFXA) (fl := fl) (n := n) (pl := pl) (BA := BA) (prefix := prefix) (body := body));
[ mk_tinv | exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
Qed.
End PrintfCore.
End F_printf_core_t3.

Module F_printf_core_t6.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_postq := (X1fq.out_postq (St:=St) Fp B BS SINK q gp tp lo canary).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_T6 := (X1fq.S_T6 (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_T6 : S_T6.
Proof using BS0 GLO HA HAP HOUT HVA LO QHI SEP_B SEP_F SFL SFR TOK TQ.
intros fuel HH xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s8 s9 t3 t4 t5 t6 Ft fc m st k i4 c w wq pq args PFXA fl n pl BA prefix body alo ahi j128 digs pad _
TI FRM FOK Hc Hw Hwq Hcw.
dest_tinv TI body prefix. cbv delta [tregs].
unfold mpad, LEFT_ADJ, ZERO_PAD. change (Z.lor 8192 65536) with 73728%Z. rewrite (pad_test_xor fl 8192) by reflexivity.
ienter. zs. zs. brf K1.
-
rewrite (proj2 (Z.eqb_neq _ _) K1). cbn [negb orb].
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
- rewrite K1, Z.eqb_refl. cbn [negb orb].
zs. zs. brf K2.
+
rewrite (proj2 (Z.leb_le _ _)) by lia.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
+ rewrite (proj2 (Z.leb_gt _ _)) by lia.
destruct (Z.leb_spec0 256 (wq - (pl + pq))) as [|N256]; [ileave; apply implM_unr_l|].
set (n4 := (wq - (pl + pq))%Z) in *.
zs. zs. try rewrite (swrap32_small (wq - (pl + pq))) by lia. fold n4.
zs. zs. zs. brf K3; [|exfalso; try rewrite unsigned_lit in K3 by lia; lia].
zs. zs.

apply (rw_cells_split_CB rsegs _ _ [] 256 _ [] [Z.to_nat n4; 256 - Z.to_nat n4]%nat) in PAD; [ | cbn; lia ].
cbn [mk_CB_cells app] in PAD.
apply (proj1 (rw_cells_app rsegs _ _ [_] _)) in PAD. destruct PAD as [PADa PADb].
cbn [cells_size csize] in PADb. rewrite Nat.add_0_r, Z2Nat.id in PADb by lia.
zs. callx (eapply memset_callZ; [exact PADa | exact MI | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | (clear - K2 LP LB LU LZB body prefix pl pq wq w QHI GLO LO slots fmt lo q; lia) | lia | (clear - N256 K2 LP Hwq body prefix pl pq wq w; lia)]).
fix_rsegs. rename MI0 into MI.
match goal with H : rw_cells _ _ (q + -368)%Z [CB (Z.to_nat n4) (repeat _ _)] |- _ => rename H into PADa end.
rewrite (Z.mod_small 32 256) in PADa by lia.
zs. brf K4; [|exfalso; try rewrite unsigned_lit in K4 by lia; (clear - K4 K3 LP LB LU LZB n4 body prefix pl pq wq w slots fmt; lia)].
destruct (SFL _ _ HS) as (fb & FLC & FB). zs. zs. zs. br K5. clear FLC.
zs. zs. zs. zs.
pose proof (rw_cells_bytes_at' _ _ _ _ PADa) as SRC. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
out_call.
1:{ unfold zb, zrepeat. rewrite map_repeat. exact SRC. }
1:{ unfold zrepeat. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. reflexivity. }
1:{ lia. } 1:{ lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
1:{ unfold zlength, zrepeat. rewrite repeat_length, Z2Nat.id by lia. lia. }
lazymatch goal with |- forall _ _ _, _ -> _ => idtac end.
match goal with |- context [out_postq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm] => out_ret mm end.
zs.

match goal with Ha : rw_cells _ ?mm (q + -368)%Z [CB (Z.to_nat n4) ?l1], Hb : rw_cells _ ?mm (q + -368 + n4)%Z [CB _ ?l2] |- _ =>
assert (PAD : rw_cells rsegs mm (q + -368) ([] ++ [CB (Z.to_nat n4) l1; CB (256 - Z.to_nat n4) l2] ++ []));
[ cbn [app]; apply (proj2 (rw_cells_app rsegs _ _ [_] _)); split; [exact Ha|]; cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact Hb
| apply rw_cells_merge in PAD; cbn [cells_size cells_bytes csize cbytes app] in PAD; rewrite app_nil_r in PAD;
replace (Z.to_nat n4 + (256 - Z.to_nat n4 + 0))%nat with 256%nat in PAD by lia; clear Ha Hb ]
end.
stmt HH as NXH.
jumpM (eapply NXH with (i := i4) (cnt := c) (l := wq) (k := k));
[ mk_finv | unfold lo_cells, ssp_guard; exact LOW | exact DIG | exact PAD | | exact APC | lia | exact AOK | exact FPC
| exact FRM | exact FOK | lia | lia | lia | unfold INT_MAX; lia ].
match goal with H : SINK _ _ |- _ => exact H end.
Qed.
End PrintfCore.
End F_printf_core_t6.

Module F_printf_core_cvd.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X1fq.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_D := (X1fq.S_CV_D (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_FMTU : S_FMTU.

Lemma fl_shl52 : forall fl, (0 <= fl < 131072)%Z ->
(Z.land (Z.shiftl fl 52) 18446744073709551615 < 9223372036854775808 <-> Z.land fl 2048 = 0)%Z.
Proof using .
clear. intros fl Hfl. rewrite Z.shiftl_mul_pow2 by lia.
change 2048%Z with (2^11)%Z. rewrite zb_land_pow2 by lia.
change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; Z.div_mod_to_equations; nia.
Qed.

Lemma L_CV_D : S_CV_D.
Proof using BS0 GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp i pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hi.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
pose proof (Z.mod_pos_bound i (2^64) ltac:(lia)) as RA.
set (argi := (i mod 2^64)%Z) in *.
unfold INTMAX_MAX, MARK_POS, PAD_POS.
ienter.
zs. zs. brf K1.
-
zs. zs. zs. zs. zs. zs. zs. zs.
replace (Z_to_bv 64 (0 - argi)) with (Z_to_bv 64 ((- argi) mod 2 ^ 64)) in * by (apply Z_to_bv_eqm; rewrite Z.mod_mod by lia; f_equal; lia).
replace (9223372036854775807 <? argi)%Z with true by (symmetry; apply Z.ltb_lt; lia).
pose proof (Z.mod_pos_bound (- argi) (2^64) ltac:(lia)) as RB.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := ((- argi) mod 2 ^ 64)%Z) (prefix := [45%Z]) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
- replace (9223372036854775807 <? argi)%Z with false by (symmetry; apply Z.ltb_ge; lia).
zs. zs. zs. zs. zs. brf K2.
+
assert (HM : Z.land fl 2048 <> 0%Z) by (intros E; apply (proj2 (fl_shl52 fl Hfl)) in E; lia).
replace (Z.land fl 2048 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact HM). cbn [negb].
zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [43%Z]) (PFXA := 66275%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 1 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
+ assert (HM : Z.land fl 2048 = 0%Z) by (apply (proj1 (fl_shl52 fl Hfl)); lia).
replace (Z.land fl 2048 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; exact HM). cbn [negb].
zs. zs. zs. zs. zs.
pose proof (land_bound' fl 1 ltac:(lia) ltac:(lia)) as B1.
assert (C1 : (Z.land fl 1 = 0 \/ Z.land fl 1 = 1)%Z).
{ pose proof (Z.land_ones fl 1 ltac:(lia)) as E. change (Z.ones 1) with 1%Z in E. change (2^1)%Z with 2%Z in E. rewrite E.
pose proof (Z.mod_pos_bound fl 2 ltac:(lia)). lia. }
destruct C1 as [E1 | E1]; rewrite E1 in *.
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := []) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 0 0 MIq ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
*
cbn [Z.eqb negb Z.mul Z.add].
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := argi) (prefix := [32%Z]) (PFXA := 66276%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros mq MIq; exact (pfx_sub mq 2 1 MIq ltac:(lia)) | repeat constructor; lia | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.
End PrintfCore.
End F_printf_core_cvd.

Module F_printf_core_scan.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_SCAN := (X1fq.S_SCAN Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Notation SPv := (Z_to_bv 64 (q + -544)).
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_LOOP1 : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(Ft : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (i n : Z) (Q : machine_state -> Prop) (k : nat) (j : Z),
finv m ->
k = Z.to_nat (n - j) -> (0 <= j)%Z -> (j < n \/ (j = n /\ znth fmt (i + n) = 37))%Z ->
(0 <= i)%Z -> (i + n < zlength fmt)%Z ->
(forall j, 0 <= j < n -> znth fmt (i + j) <> 0 /\ znth fmt (i + j) <> 37)%Z ->
(znth fmt (i + n) = 0 \/ (znth fmt (i + n) = 37 /\ i + n + 1 < zlength fmt /\ znth fmt (i + n + 1) <> 37))%Z ->

(forall a0, evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) a0 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 (if (znth fmt (i + n) =? 0)%Z then 0x35430 else 0x35438)) fc None m (seg_rom rsegs))) ->
evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (znth fmt (i + j))) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (A + i + j)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x35420) fc None m (seg_rom rsegs)).
Proof using HF.
intros until k. induction k as [|k IH]; intros j FI Hk Hj Hjn Hi Hin LIT TERM HK.
-
assert (j = n) by lia. subst j. destruct Hjn as [|[_ T37]]; [lia|].
dest_finv FI. unfold INT_MAX in *.
zs. rewrite T37. if_lit. specialize (HK (Z_to_bv 64 37)). rewrite T37, (proj2 (Z.eqb_neq 37 0)) in HK by lia. exact HK.
- destruct Hjn as [Hjn|[Hjn _]]; [|exfalso; lia].
pose proof (LIT j ltac:(lia)) as [NZ N37].
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
pose proof (fmt_rng (i + j) ltac:(unfold zlength in *; lia)) as RG0.
zs. br K.
rd_fmt (i + j + 1)%Z. zs. fix_u8 (i + j + 1)%Z. zs. zs.
destruct (Z.lt_ge_cases (j + 1) n) as [Hlt|Hge].
+
pose proof (LIT (j + 1)%Z ltac:(lia)) as [NZ1 _]. replace (i + j + 1)%Z with (i + (j + 1))%Z in * by lia.
br K1. replace (A + i + j + 1)%Z with (A + i + (j + 1))%Z by lia.
eapply (IH (j + 1)%Z FI'); try lia; try assumption.
+ assert (j + 1 = n)%Z by lia. replace (i + j + 1)%Z with (i + n)%Z in * by lia.
replace (A + i + j + 1)%Z with (A + i + n)%Z by lia.
destruct TERM as [T0 | (T37 & Hn1 & T1)].
* rewrite T0. if_lit. specialize (HK (Z_to_bv 64 0)). rewrite T0, Z.eqb_refl in HK. exact HK.
* br K1. eapply (IH n FI'); try (clear - H LZB Hjn Hk j k n fmt Hj T37 i Hi Hn1 K1 RG T1; lia); try assumption.
Qed.

Lemma L_SCAN : S_SCAN.
Proof using A0 HA HF.
intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m i n cnt' Q _
FI Hi Hn Hin LIT TERM Hnz Hc Hnc HK.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *.
assert (NZ0 : znth fmt i <> 0%Z).
{ destruct Hnz as [Hp|H37]; [|rewrite H37; lia]. pose proof (LIT 0%Z ltac:(lia)) as [X _]. rewrite Z.add_0_r in X. exact X. }
pose proof (fmt_rng i ltac:(unfold zlength in *; lia)) as RGi.
zs. zs. br K.
eapply evt_eq; [ | eapply L_LOOP1 with (i := i) (n := n) (k := Z.to_nat (n - 0)) (j := 0%Z); try exact FI'; try lia; try assumption ].
{ cbv delta [mkR]. rewrite !Z.add_0_r. reflexivity. }
{ destruct Hnz as [Hp|H37]; [left; lia|]. destruct (Z.lt_ge_cases 0 n); [left; lia|]. right. split; [lia|]. replace (i + n)%Z with i by lia. exact H37. }
intros a0.

assert (TL : forall a1 a2, evt rsegs Q
(MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 37) (Z_to_bv 64 2147483647) (Z_to_bv 64 (A + i + n)) a1 a2 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 cnt') x20 (Z_to_bv 64 (A + i + n)) x22 (Z_to_bv 64 (A + i)) x24 x25 x26 x27 x28 x29 x30 x31)
Ft (Z_to_bv 64 0x35464) fc None m (seg_rom rsegs))).
{ intros a1 a2. zs. replace (A + i + n - (A + i))%Z with n by lia. zs. fixr. zs. br K1. zs. fixr. apply HK. }
destruct TERM as [T0 | (T37 & Hn1 & T1)].
- rewrite T0, Z.eqb_refl. zs. zs. apply TL.
- rewrite T37. cbn [Z.eqb Pos.eqb]. zs. zs. rd_fmt (i + n + 1)%Z. zs. fix_u8 (i + n + 1)%Z. zs. br K1. zs. apply TL.
Qed.
End PrintfCore.
End F_printf_core_scan.

Module F_printf_core_flags.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_FLAGS := (X1fq.S_FLAGS Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_FLAGS : S_FLAGS.
Proof using HF.
intros x1 x6 x7 x10 x11 x12 x15 x18 x19 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q p k fl b w3 FL s1 _
FI Hp Hk Hpk Hw3 Hfl Hb PF NE HK.
remember (Z.to_nat (zlength fmt - (p + k))) as kk eqn:Hkk.
revert k fl b w3 x11 x12 x15 Hk Hpk Hw3 Hfl Hb PF HK Hkk.
induction kk as [|kk IH]; intros.
{   rewrite sfx_nil in PF by (unfold zlength in *; lia). cbn in PF. injection PF as _ <-. exfalso. apply NE. reflexivity. }
assert (Hlt : (p + k < zlength fmt)%Z) by (unfold zlength in *; lia).
pose proof FI as FI'. dest_finv FI.
zs. rd_fmt (p + k)%Z. zs. fix_u8 (p + k)%Z. zs. zs. rewrite Hw3. zs. brf K.
-
assert (NF : flag_bit (znth fmt (p + k)) = None).
{ destruct (flag_bit (znth fmt (p + k))) eqn:E; [|reflexivity]. exfalso.
pose proof (flag_bit_range (znth fmt (p + k)) ltac:(congruence)) as R.
pose proof (proj2 (sp_test (znth fmt (p + k)) RG) R). lia. }
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
- assert (Hc : (32 <= znth fmt (p + k) < 64)%Z) by (apply (proj1 (sp_test _ RG)); exact K).
rewrite (land_M64_id (znth fmt (p + k) + -32)) in * by lia.
zs. zs. zs. zs. brf K2.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
destruct (flag_bit (znth fmt (p + k))) as [b'|] eqn:E.
2:{ exfalso. apply (proj2 (flag_none _ Hc)) in E. lia. }
pose proof (flag_some _ _ Hc E) as [Hfw Hb'].
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_some _ _ _ _ E) in PF.
replace (A + p + k + 1)%Z with (A + p + (k + 1))%Z by lia.
rewrite Z.lor_comm.
eapply (IH (k + 1)%Z (Z.lor fl b) b'); try (clear - Hk k Hlt p fmt Hb' b' LZB Hkk kk; lia).
{ rewrite unsigned_lit_land. exact Hfw. }
{ apply lor_bound17; lia. }
{ replace (p + (k + 1))%Z with (p + k + 1)%Z by lia. exact PF. }
{ intros k' c' a3 a4 a5 Hk' Hs1 Hc' HN HFL. eapply HK; try eassumption; lia. }
all: unfold zlength in *; lia.
+
change (Z.land (bv_swrap 32 (Z.shiftl 1 ((znth fmt (p + k) + -32) mod 32))) 18446744073709551615) with (flagw (znth fmt (p + k))) in K2.
assert (NF : flag_bit (znth fmt (p + k)) = None) by (apply (proj1 (flag_none _ Hc)); lia).
rewrite (sfx_cons fmt (p + k)) in PF by (unfold zlength in *; lia). rewrite (parse_flags_cons_none _ _ _ NF) in PF.
injection PF as EFL Es1.
rewrite Z.lor_comm, EFL.
jump (eapply (HK (p + k)%Z (znth fmt (p + k))); try reflexivity; try assumption; try lia).
{ rewrite (sfx_cons fmt (p + k)) by (unfold zlength in *; lia). symmetry. exact Es1. }
rewrite <- EFL. apply lor_bound17; lia.
Qed.
End PrintfCore.
End F_printf_core_flags.

Module F_printf_core_xloop.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation xloop_post := (X1fq.xloop_post q gp tp).
Local Notation S_XLOOP := (X1fq.S_XLOOP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_XLOOP : S_XLOOP.
Proof using GLO LO QHI.
intros x1 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m l x.
remember (Z.to_nat x) as nx eqn:Enx. revert x Enx x12 x13 x23 m.
induction nx as [nx IH] using lt_wf_ind.
intros x Enx x12 x13 x23 m j ds _ MI DIG Hx Hl Hj ->.
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO.
pose proof (munch_refl [(q + -392, q + -368)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (hex_digits_step l x ltac:(lia)) as DS.
pose proof (Z.div_pos x 16 ltac:(lia) ltac:(lia)) as Q0.
pose proof (Z.mod_pos_bound x 16 ltac:(lia)) as R0.
assert (Q1 : (x / 16 < 1152921504606846976)%Z) by (apply Z.div_lt_upper_bound; lia).
assert (LD : (1 <= zlength (hex_digits l x))%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
pose proof (rw_CB_length _ _ _ _ DIG) as LDS.
pose proof (hexchar_range 0 (x mod 16)%Z ltac:(lia) ltac:(lia)) as XR. rewrite Z.lor_0_r in XR.
pose proof (hexchar_range l (x mod 16)%Z Hl ltac:(lia)) as HR.
zs. zs. zs. zs.
replace (Z.land x 15) with (x mod 16)%Z in * by (change 15%Z with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
pose proof (xdigits_read _ (x mod 16)%Z MI ltac:(lia)) as RD.
zs. cbv beta. rewrite (u8_lit (znth XDIGITS (x mod 16))) by lia.
zs. replace (Z.shiftr x 4) with (x / 16)%Z by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
zs. try rewrite (land_W64_small (znth XDIGITS (x mod 16))) by lia.
set (c := Z.lor (znth XDIGITS (x mod 16)) l) in *.
pose proof (u8arr_of_rw_cells _ _ _ _ _ DIG) as DA.
pose proof (u8arr_store_ok rsegs _ _ _ (j - 1)%Z (wa (q + -392 + j + -1)) DA ltac:(rewrite LDS; lia) ltac:(f_equal; lia)) as SOK.
zs. rewrite le1_small by lia. replace (q + -392 + j + -1)%Z with (q + -392 + (j - 1))%Z by lia.
pose proof (u8arr_write rsegs _ _ _ (j - 1)%Z (Z_to_bv 8 c) DA ltac:(rewrite LDS; lia)) as DA2. clear DA. store_done.
pose proof (rw_cells_of_u8arr _ _ _ _ DA2) as DIG1. rewrite upd_length, LDS in DIG1.
zs. zs. brf K.
-
eapply evt_mono.
{ eapply (IH (Z.to_nat (x / 16)) ltac:(lia) (x / 16)%Z eq_refl) with (j := (j - 1)%Z); [ exact MI | exact DIG1 | lia | exact Hl | | f_equal; lia ].
rewrite DS in Hj. unfold zlength in *. rewrite length_app in Hj. cbn [length] in Hj. lia. }
cbv beta. intros ms' P. first [ sf_destruct 9%nat P as a2' a3' m' -> MU' WM' MI' DIG' HW | sf_fb; destruct P as (a2' & a3' & m' & -> & MU' & WM' & MI' & DIG' & HW) ].
unfold xloop_post. first [ unshelve sf_eexists 3%nat; [ exact (a2') | exact (a3') | exact (m') | ] | sf_fb; exists a2', a3', m' ]. cbv zeta.
assert (EL : zlength (hex_digits l x) = (zlength (hex_digits l (x / 16)) + 1)%Z) by (rewrite DS; unfold zlength; rewrite length_app; cbn [length]; lia).
rewrite EL.
split; [ mseq | ].
split; [ eapply munch_trans; [exact MU | exact MU'] | ].
split; [ eapply wmono_trans; [exact WM | exact WM'] | ].
split; [ exact MI' | ].
split.
{ replace (firstn (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds)
with (firstn (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)) ++ zb (hex_digits l (x / 16)) ++ skipn (Z.to_nat (j - 1)) (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c))); [exact DIG'|].
rewrite upd_firstn_part by (rewrite LDS; unfold zlength in *; lia). rewrite upd_skipn_at by (rewrite LDS; lia).
replace (Z.to_nat (j - 1 - zlength (hex_digits l (x / 16)))) with (Z.to_nat (j - (zlength (hex_digits l (x / 16)) + 1))) by lia.
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia.
rewrite DS, zb_app, <- !app_assoc. reflexivity. }
unfold zlength in *. lia.
-
apply evt_done. unfold xloop_post. sf_eexists 3%nat. cbv zeta.
assert (E0 : hex_digits l (x / 16) = []) by (replace (x / 16)%Z with 0%Z by lia; apply hex_digits_0).
assert (EL : zlength (hex_digits l x) = 1%Z) by (rewrite DS, E0; reflexivity).
rewrite EL.
split; [ mseq | ].
split; [ exact MU | ]. split; [ exact WM | ]. split; [ exact MI | ].
split.
{ replace (firstn (Z.to_nat (j - 1)) ds ++ zb (hex_digits l x) ++ skipn (Z.to_nat j) ds) with (upd ds (Z.to_nat (j - 1)) (Z_to_bv 8 c)); [exact DIG1|].
rewrite upd_firstn_skipn by (rewrite LDS; lia). rewrite DS, E0. cbn [zb map app].
replace (S (Z.to_nat (j - 1))) with (Z.to_nat j) by lia. reflexivity. }
lia.
Qed.
End PrintfCore.
End F_printf_core_xloop.

Module F_printf_core_state.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation S_STATE := (X1fq.S_STATE Fp B BS ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Lemma L_STATE : S_STATE.
Proof using HF.
intros x1 x5 x6 x7 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Ft fc m Q k3 ty _ FI Hk3 CT HK.
pose proof FI as FI'. dest_finv FI.
pose proof (conv_type_range _ _ CT) as TR. pose proof (conv_type_ty _ _ CT) as TY.
zs. zs. rd_fmt k3. zs. fix_u8 k3. zs. zs. brf K.
{ exfalso. rewrite land_M64_neg in K by lia. lia. }
clear K. zs. zs. zs. zs. zs. zs.
pose proof (states0_read m _ _ MI CT) as RD2. zs. cbv beta. rewrite (u8_lit ty) by lia.
zs. zs. zs. brf K2. { exfalso. try rewrite land_M64_id in K2 by lia. lia. }
clear K2. zs. zs. brf K3. { exfalso. try rewrite land_M64_id in K3 by lia. lia. }
clear K3. zs. brf K4. { exfalso. try rewrite land_M64_id in K4 by lia. lia. }
clear K4. zs. br K5.
jump (apply HK).
Qed.
End PrintfCore.
End F_printf_core_state.

Module F_printf_core_cvu.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Open Scope bv_scope.
Set Warnings "-notation-for-abbreviation".

Section PrintfCore.
Context {RCEIL : RunCeiling}.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Context {St : Type}.
Variables (Fp B BS : Z) (SINK : (word -> option byte) -> St -> Prop) (TOPOK : Z -> Prop)
(OUT : list Z -> M St unit) (OUTFP : Z -> Z -> Z -> Z -> Z -> M St Z).
Hypothesis SFR : sink_frame_stmt Fp B BS SINK.
Hypothesis SFL : sink_flags_stmt Fp SINK.
Hypothesis TOK : topok_stmt TOPOK.
Hypothesis HOUT : out_stmt Fp B BS SINK TOPOK OUT.
Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
(F : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte)
(lo : Z) (canary : word) (A : Z) (fmt : list Z) (AP VA : Z) (slots : list word) (nla nlt : word).
Hypothesis HF : Forall (fun c => 0 <= c < 256)%Z fmt.
Hypothesis LO : (lo <= q - PC_DEPTH)%Z.
Hypothesis GLO : (GLOBALS_TOP <= lo)%Z.
Hypothesis QHI : (q < 2^63)%Z.
Hypothesis TQ : TOPOK q.
Hypothesis FRM0 : frm0 fc0.

Hypothesis HA : (A + zlength fmt <= 131072)%Z.

Hypothesis SEP_F : ((245976 <= Fp /\ Fp + 232 <= 448184) \/ (AP + 8 <= Fp /\ Fp + 232 <= VA))%Z.
Hypothesis SEP_B : ((448192 <= B /\ B + BS <= lo) \/ (AP + 8 <= B /\ B + BS <= VA))%Z.
Hypothesis HAP : (q <= AP)%Z.
Hypothesis HVA : (AP + 8 <= VA)%Z.
Hypothesis A0 : (0 <= A)%Z.
Hypothesis VAHI : (VA + 8 * zlength slots <= 2^64)%Z.
Hypothesis BS0 : (0 <= BS)%Z.

Local Notation W := (X1fq.W Fp B BS q lo AP).
Local Notation hi_cells := (X1fq.hi_cells ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e canary).
Local Notation lo_cells := (X1fq.lo_cells AP nla nlt).
Local Notation finv := (X1fq.finv Fp B BS ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots).
Local Notation fmt_rng := (X1fq.fmt_rng fmt HF).
Local Notation implM_eq_ms := (X1fq.implM_eq_ms (St:=St)).
Local Notation sink_store := (X1fq.sink_store (St:=St) Fp B BS SINK SFR).
Local Notation sink_call := (X1fq.sink_call (St:=St) Fp B BS SINK SFR).
Local Notation out_callq := (X1fq.out_callq (St:=St) Fp B BS SINK TOPOK OUT TOK HOUT q gp tp lo canary fmt AP VA slots LO GLO QHI TQ SEP_F SEP_B HAP BS0).
Local Notation body_loc := (X1fq.body_loc Fp B BS q lo).
Local Notation tregs := (X1fq.tregs Fp q gp tp A).
Local Notation tinv := (X1fq.tinv (St:=St) Fp B BS SINK TOPOK OUTFP ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_FMTU := (X1fq.S_FMTU (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).
Local Notation S_CV_U := (X1fq.S_CV_U (St:=St) Fp B BS SINK TOPOK OUT OUTFP ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc0 m0 lo canary A fmt AP VA slots nla nlt).

Notation qq := (q + -544)%Z.
Ltac hush := idtac.
Ltac seps := idtac.
Ltac seps_all := idtac.
Ltac zs := hush; zstep; try (fix_litstore; mem_after_store_opt).
Ltac zst := hush; seps; zstep; try (fix_litstore; mem_after_store_opt); hush.
Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FRhi := fresh "FRhi" in
let ST := fresh "ST" in let BY := fresh "BY" in let VAA := fresh "VAA" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
sf_curry 9%nat H; intros MI MU WM FRhi ST BY VAA SSP1 SSP2; sf_clear H; sf_fix_order; unfold W in MU; unfold hi_cells in FRhi;
unfold got_ssp, ssp_guard in SSP1, SSP2; unfold va_area in VAA;
unfold PC_DEPTH, GLOBALS_TOP in LO, GLO;
try (let LT := fresh "LZB" in pose proof (zb_length fmt) as LT;
lazymatch goal with _ : length (zb fmt) = length fmt, _ : length (zb fmt) = length fmt |- _ => clear LT | _ => idtac end);
try (let LT := fresh "LU" in pose proof (u64s_length slots) as LT;
lazymatch goal with _ : length (u64s slots) = _, _ : length (u64s slots) = _ |- _ => clear LT | _ => idtac end);
unfold zlength in *; hush.
Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.
Ltac mk_finv := unfold finv, W, hi_cells, got_ssp, ssp_guard, va_area;
split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [first [hyp | hyp_cells] |]; split; [hyp|]; split; [hyp|]; split; hyp.
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q0) _ _ _ _) => constr_eq q0 p end.
Ltac zsto p := repeat (tryif at_pc p then fail else
lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zs end).
Ltac fix_u8 i := cbv beta; rewrite (u8_lit (znth fmt i)) by (apply fmt_rng; unfold zlength in *; lia).
Ltac rd_fmt idx :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
match goal with BYH : bytes_at _ m A (zb fmt) |- _ =>
let RD := fresh "RD" in let RG := fresh "RG" in
pose proof (zbytes_read m A fmt idx _ BYH ltac:(unfold zlength in *; lia) eq_refl) as RD;
pose proof (fmt_rng idx ltac:(unfold zlength in *; lia)) as RG;

repeat match type of RD with context [(?a + (?b + ?c))%Z] =>
replace (a + (b + c))%Z with (a + b + c)%Z in RD by lia end
end end.
Ltac the_mi k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => match goal with M : mem_inv _ m |- _ => k M end end.
Ltac mseq := cbv delta [mkR]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Tactic Notation "jump" tactic3(tac) := eapply evt_eq; [ | tac ]; [ mseq | .. ].
Tactic Notation "jumpM" tactic3(tac) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
eapply implM_eq_ms; [ | tac ]; [ mseq | .. ].
Ltac stmt H := let NX := fresh "NX" in pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.
Tactic Notation "stmt" constr(H) "as" ident(NX) := pose proof H as NX; let T := type of NX in let T' := eval red in T in change T' in NX.

Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ apply (sink_store m st a bs) in H; [ | exact Ha | rewrite Hn; exact Hl | rewrite Hn; tslia | rewrite Hn; tslia ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from store):" H; clear H ]
end.
Local Ltac transport_call_extra segs W m m' MU WM ::=
repeat match goal with
| H : SINK m ?st |- _ =>
first [ eapply (sink_call W m m' st) in H;
[ | exact MU | exact WM
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil
| repeat (apply Forall_cons; [ cbn [fst snd]; tslia | ]); apply Forall_nil ]
| idtac "note: dropping SINK hypothesis (not provably disjoint from callee footprint):" H; clear H ]
end.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3.
Ltac out_call :=
ileave; eapply implM_bind;
[ eapply out_callq;
[ match goal with H : SINK _ _ |- _ => exact H end
| | |
| match goal with H : stk _ _ _ _ |- _ => exact H end
| unfold ssp_cells, got_ssp, ssp_guard; split;
[ match goal with H : rw_cells _ _ 245968 _ |- _ => exact H end
| match goal with H : rw_cells _ _ 448184 _ |- _ => exact H end ]
| match goal with H : mem_inv _ _ |- _ => exact H end
| | | | | | ]
| cbv beta ].
Ltac out_ret m :=
let st' := fresh "st" in intros [] st'; post_call rsegs m;
try (let MIn := fresh "MI" in match goal with H : mem_inv _ _ |- _ => rename H into MIn end);
ienter;
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
Ltac fix_rsegs := cbv delta [X1fd.rsegs X1fc.rsegs] in *; fold X1ff.rsegs in *.
Ltac mseq ::= cbv delta [mkR tregs]; repeat first [ reflexivity | lazymatch goal with |- @eq ?T _ _ => lazymatch T with Z => zl | nat => zl end | |- _ => zl end | progress f_equal | zl ].
Ltac dest_tinv H body prefix :=
let FI := fresh "FI" in
sf_curry 25%nat H; intros FI LOW DIG PAD HS APC Hk AOK FPC BODY BRNG BLOC BHI Hn HPFX PRNG PF0 PF1 Hpl PL2 Hi4 Hfl HnI Hnp Hplp; sf_clear H; sf_fix_order;
pose proof FI as FI'; dest_finv FI; unfold lo_cells, ssp_guard in LOW; unfold body_loc in BLOC; unfold INT_MAX in *;
pose proof (zb_length body) as LB; pose proof (zb_length prefix) as LP;
let BB := fresh "BB" in pose proof (bytes_at_bound _ _ _ _ BODY) as BB; rewrite LB in BB.
Ltac mk_tinv :=
lazymatch goal with |- tinv ?m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
unfold tinv, body_loc;
split; [mk_finv|];
split; [unfold lo_cells, ssp_guard; first [hyp | hyp_cells] |];
split; [match goal with H : rw_cells _ m (q + -392)%Z _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m (q + -368)%Z _ |- _ => exact H end |];
split; [match goal with H : SINK m _ |- _ => exact H end |];
split; [match goal with H : rw_cells _ m AP _ |- _ => exact H end |];
split; [lia|];
split; [assumption|];
split; [assumption|];
split; [match goal with H : bytes_at _ m _ (zb _) |- _ => exact H end |];
repeat (split; [first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl] |]); first [assumption | reflexivity | lia | zl | unfold INT_MAX in *; zl]
end.

Hypothesis HS_FMTU : S_FMTU.

Lemma L_CV_U : S_CV_U.
Proof using GLO HA HAP HS_FMTU HVA LO QHI SEP_B SEP_F SFR.
intros fuel HH x1 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x26 x27 x28 x29 x30 x31 Ft fc m st i4 k c args fl w p xp u pfx s2s za pl plp ahi j128 digs pad _
FI LOW DIG PAD HS APC Hk AOK FPC FRM FOK Hi4 Hfl Hw Hc XP Hu.
pose proof FI as FI'. dest_finv FI. unfold INT_MAX in *. unfold lo_cells, ssp_guard in LOW.
stmt (HS_FMTU fuel HH) as NX.
ienter.
zs. zs. zs. zs. zs. zs.
jumpM (eapply NX with (i4 := i4) (k := k) (c := c) (args := args) (fl := fl) (w := w) (p := p) (xp := xp) (x := u) (prefix := []) (PFXA := 66274%Z));
[ mk_finv | exact LOW | exact DIG | exact PAD | exact HS | exact APC | lia | exact AOK | exact FPC | exact FRM | exact FOK
| intros m' MI'; exact (pfx_sub m' 0 0 MI' ltac:(lia)) | apply Forall_nil | lia | zl | zl | zl | lia | unfold INT_MAX; lia | unfold INT_MAX; lia | exact XP | lia ].
Qed.
End PrintfCore.
End F_printf_core_cvu.
