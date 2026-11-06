(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH Qtgi Qsw7 QJjn QKQo QPZI QlCE QhHQ Q5Ki QRUw QmZZ QkMG Qu4M QG8z Qdyh Q2Sr QLbz Q6WR QrPc Q7UD QXUB Qhd4 Qwm6 QlKV Q30W QsKa Qiiq Q1Ey Ql4f Q1Y6 QrQv QGdd QdGy QcmL QV7s QYZ0 QQ2r QtyQ Q8l1 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QRUw.Mq2 QmZZ QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz QLbz.Mq0.
Import Q6WR.Mq0 QrPc.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QlKV.Mq7 Q30W.Mq3 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd QdGy.Mq0 QcmL.Mq0 QsKa.Mq8 QrQv.Mq2 QV7s QYZ0.Mq4 QdGy QQ2r.Mq4 QYZ0.Mq2 QtyQ.Mq4.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_ISTRLEN : Z := 0x4f950.
Definition A_PE_ENTRY : Z := 0x930e8.
Definition A_GOT_PEPC : Z := 0xe6a78.
Definition PE_STK_A : Z := 432 + 12288.

Section PeSEntry.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Notation HEAPAx := (HEAPA A4L HIx).
Definition rtc_pepc_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_PEPC (le8 (Z_to_bv 64 A_PE_ENTRY)).
Hypothesis RTC_PEPC : rtc_pepc_stmt.

Definition heapA_errno_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> exists errv, rw_cells asegs m A_ERRNO [C4 errv].
Hypothesis OBL_ERRNO : heapA_errno_stmt.

Lemma presx_private : forall A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (LOCCELL_A <= fst iv /\ snd iv <= LOCCELL_A + 8)) W ->
heap_presx A4H xlocA L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn [fst snd] in H1.
assert (OLD : ((alloc_ceiling <= lo /\ hi <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= lo /\ hi <= a + n)
\/ (forall x, lo <= x < hi -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= lo /\ hi <= F + fr_size k) \/ (shad A4L F <= lo /\ hi <= shad A4L F + fr_shadow_len k)))) -> ~ (lo <= a < hi)).
{ intros H1'. pose proof (client_outsideF HIx A LBall LM FR B L0 m md [(lo, hi)] SP HP Hsub HSP
ltac:(apply Forall_cons; [exact H1' | apply Forall_nil]) a Ha (client_addrx_addr A4H _ _ _ _ Hc)) as Ho.
cbn [outside] in Ho. exact (proj1 Ho). }
destruct H1 as [H1 | [H1 | [H1 | H1]]]; [apply OLD; left; exact H1 | apply OLD; right; left; exact H1 | apply OLD; right; right; right; exact H1 |].
intros Hin. pose proof alloc_ceiling_range as ACR. unfold LOCCELL_A, A_TP in H1.
destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- lia.
- apply Hx. right. unfold LOCCELL_A, A_TP. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr. destruct (Hsub _ Hb) as [Hb' | Hb'].
+ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP Hb') as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr. Z.div_mod_to_equations. lia.
Qed.

Definition sh_errno_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m (A_ERRNO / 8 + A_SB) [Z_to_bv 8 0].
Hypothesis OBL_SH_ERRNO : sh_errno_stmt.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.

Definition istrlen_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a lo : Z) (s slack : list byte) (Q : machine_state -> Prop),
unpoisoned asegs m A_SB a (Z.of_nat (length s) + 1) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= 2^47 -> Z.of_nat (length s) + 1 < 2^40 ->
(64 < Z.of_nat (length s) + 1 -> app_mem a (Z.of_nat (length s) + 1)) ->
(a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= a) ->
a0 = Z_to_bv 64 a -> ~ In (Z_to_bv 8 0) s ->
bytes_at asegs m a (s ++ Z_to_bv 8 0 :: slack) -> (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length s))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRLEN) fc None m (seg_rom asegs)).
Hypothesis ISTRLEN : istrlen_spec_U.

Definition pe_arg_okA (m : word -> option byte) (LBc : list blk) (FRS : list frame) (sb len lenr : Z) (payload slack : list byte) : Prop :=
(len = 0 \/ (exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len <= Fh + fr_size kh - 8 /\ unpoisoned asegs m A_SB sb len)) /\
(lenr = len \/
(lenr = 2^64 - 1 /\ 1 <= len /\ (exists str0, payload = str0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str0) /\
bytes_at asegs m (sb + len) slack /\ (- (sb + len)) mod 8 <= Z.of_nat (length slack) /\
((exists b, In b LBc /\ blk_addr b <= sb /\ sb + len + Z.of_nat (length slack) <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len + Z.of_nat (length slack) <= Fh + fr_size kh - 8)))).

Lemma pe_post_A_eq : forall pf pa pf' pa' sv F fc md LBc LM FRS me lo ms' md' A',
pf_tk pf = pf_tk pf' -> pf_mxd pf = pf_mxd pf' -> pf_fl pf = pf_fl pf' -> pf_len pf = pf_len pf' ->
pa_sp0 pa = pa_sp0 pa' -> pa_bslack pa = pa_bslack pa' -> pa_dslack pa = pa_dslack pa' ->
pe_post_A HIx GA pf pa sv F fc md LBc LM FRS me lo ms' md' A' -> pe_post_A HIx GA pf' pa' sv F fc md LBc LM FRS me lo ms' md' A'.
Proof.
intros pf pa pf' pa' sv F fc md LBc LM FRS me lo ms' md' A' E1 E2 E3 E7 E4 E5 E6 P. unfold pe_post_A in *. rewrite <- E1, <- E2, <- E3, <- E4, <- E5, <- E6, <- E7. exact P.
Qed.

Ltac pe_fw_solve tk Fr sh INtk INF :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; split; [exact INtk | cbn [fst snd]; lia]
| right; right; right; left; exists Fr, 2; split; [exact INF|]; left; cbn [fst snd]; rewrite fr_size_2; lia
| right; right; right; left; exists Fr, 2; split; [exact INF|]; right; cbn [fst snd]; unfold sh, shad; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; unfold A_SB; lia
| right; right; right; right; cbn [fst snd]; intros x Hx; unfold LOCCELL_A, A_TP in Hx; cbn [hl_client_static A4H]; unfold a4_client_static; lia ] | ]);
apply Forall_nil.
Ltac pe_px_solve1 tk INtk NTK :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; (split; [exact INtk|]); (split; [exact NTK|]); cbn [fst snd]; lia
| right; right; right; cbn [fst snd]; unfold LOCCELL_A, A_TP; lia ] | ]);
apply Forall_nil.
Ltac pe_px_solve tk Fr sh INtk NTK INF OFF OFS :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; (split; [exact INtk|]); (split; [exact NTK|]); cbn [fst snd]; lia
| right; right; left; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]); left; cbn [fst snd]; rewrite fr_size_2; lia
| right; right; left; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]); right; cbn [fst snd]; unfold sh, shad; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; unfold A_SB; lia
| right; right; right; cbn [fst snd]; unfold LOCCELL_A, A_TP; lia ] | ]);
apply Forall_nil.
Ltac if_lit b :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota end.
Ltac pe_img_solve := repeat (apply Forall_cons; [cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; lia | ]); apply Forall_nil.
Lemma seg_entry_A0 :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (TBS LBc LM : list blk) (FRS : list frame) (B : bud) (tk sb len lenr lo bsl dsl sp0 : Z) (payload slack : list byte) (errv : word) (mxd fl q pb : Z) (pbs : list blk),
HEAPAx A (TBS ++ LBc) LM FRS B m md ->

TBS = [(tk, 72); (q, 32 * mxd)] ++ pbs -> (1 <= mxd <= 32 /\ 0 <= fl < 2^32) ->
rw_cells asegs m tk (tok_cells_g mxd fl pb 0 q (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) ->
pbuf asegs m pbs pb -> pb <> 0 ->
tstack asegs m q (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)) ->
bytes_at asegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_okA m LBc FRS sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA m ->
sp = Z_to_bv 64 sp0 ->
stk asegs m lo sp0 -> alloc_ceiling <= lo -> lo <= sp0 - PE_STK_A ->
sp0 mod 32 = 0 -> sp0 + 32 <= hiA_top A4L HIx -> sp0 < 2^62 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->
Z.of_nat (length LM) < 8 -> Z.of_nat (length FRS) + 2 < 4096 -> M2D <= bD B ->
K_free * Z.of_nat (length TBS) + K_exit + bsl <= bB B -> M2D + dsl <= bD B -> 0 <= bsl ->
let sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 in

(forall (newl spf Ff : Z) (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud)
(nb : word) (pj : pe_junkA) (errv1 : word) (gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' t4' : word),
let pf := PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd fl in
let pa := PEFA (sp0) Ff LC_GLOBAL_A newl bsl dsl in
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LBc ((newl, 48) :: LM) FRS payload m1 lo m1 md1 A1 B1 (ts_init mxd pb pbs) (Z_to_bv 8 1) nb pj sv errv1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (sp0) m m1 ->
agree_on asegs pbs m m1 ->
rw_cells asegs m1 LOCCELL_A [C8 (Z_to_bv 64 newl)] -> 0 < newl < 2^64 ->
bB B <= bB B1 -> bD B - M2D <= bD B1 ->
AJ5 A4L HIx A1 T md1 (pe_msA asegs pf pa APE_LOOP 0 gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' (Z_to_bv 64 (tk + 56)) t4' F fc m1)) ->

(forall ms' md' A', pe_post_A HIx GA (PEF tk 0 0 len lenr sb 0 (cfg_model md) mxd fl) (PEFA (sp0) 0 0 0 bsl dsl) sv F fc md LBc LM FRS m lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_PE_ENTRY) fc None m (seg_rom asegs)).
Proof.
intros until pbs. intros HP ETBS MXB TOK PB Hpb TSK STR PLEN LEN MODE SB0 SBL LOC LCK G ESP ST LO LOS SPA HT SP62 ERR TP RAE A0 A1 A2 LMN FRN BM1 BB BD BSL sv KL KR.
unfold PE_STK_A in LOS.
subst a0 a1 a2 tp sp.
assert (INtk : In (tk, 72) ((TBS ++ LBc) ++ LM)) by (apply in_or_app; left; rewrite ETBS; left; reflexivity).
assert (INtkB : In (tk, 72) (TBS ++ LBc)) by (rewrite ETBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
pose proof (RTC_PEPC _ _ _ _ _ _ _ HP) as PEPC. apply ro_C8_of_bytes_at in PEPC. unfold A_GOT_PEPC in PEPC.
a4l.
assert (SP0R : 0 <= sp0 < 2^64) by lia.

set (LB0 := (q, 32 * mxd) :: pbs ++ LBc).
set (L0 := LB0 ++ LM ++ fr_ivs A4L FRS).
assert (INCL0 : incl LB0 (TBS ++ LBc)) by (unfold LB0; rewrite ETBS; intros b Hb; right; exact Hb).
assert (SUBa : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; apply INCL0; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (NTK : ~ In (tk, 72) L0).
{ intros Hin. unfold L0 in Hin. apply in_app_or in Hin as [Hin | Hin].
- pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite ETBS in ND. cbn [app map blk_addr fst] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. unfold LB0 in Hin.
destruct Hin as [E | Hin]; [left; injection E; intros; lia | right; rewrite map_app; apply in_or_app; left; exact (in_map blk_addr _ _ Hin)].
- apply in_app_or in Hin as [Hin | Hin]; [| exact (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INtk Hin)].
exact (nodup_prefix_suffix (TBS ++ LBc) LM tk 72 72 (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) INtkB Hin). }
pose proof (heap_presx_refl A4H xlocA L0 sp0 m) as HPX.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(sp0 - 416, sp0); (tk, tk + 72)] m) as MU.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
stash PB. stash TSK. stash STR. stash MODE. stash KL. stash KR. stash G.
unfold A_PE_ENTRY, LOCCELL_A, LOCALE_LOCK_A, A_ERRNO, A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
step. carve_frame 416%nat ST.
stepz. do 13 step. step. step.
rewrite (unsigned_lit (sp0 + -416)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (sp0 + -416 - (sp0 + -416) mod 32) with (sp0 + -416) by (clear - SPA; Z.div_mod_to_equations; lia).
step. stepz. step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX1 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP MU WM SUBa ltac:(lia)); pe_px_solve1 tk INtk NTK]);
unstash G; assert (G1 : GA mc) by (eapply GA_outside; [exact G | exact MU | exact WM | pe_img_solve]); clear G
end.
clear HPX.
evt_done5.
eapply (hiA_stack_malloc A4L HIx) with (k := 2) (bytes := 224) (lo := lo) (LB := TBS ++ LBc) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | (clear - FRN; lia) | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (OBL_ERRNO _ _ _ _ _ _ _ HP1) as (errv1 & ERR1).
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (HPX2 : heap_presx A4H xlocA L0 sp0 m m1').
{ eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR1 | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply INCL0; exact Hb | apply in_or_app; right; exact Hb]. }
assert (G2 : GA m1') by (eapply GA_pres; [exact HPR1 | exact G1]).
clear HPX1 G1.

assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ tk 72 HP1 INtk) as APt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INtk) as DFt.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp, DFt. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp, APt.
destruct (own_frame_freshG HIx Fr (TBS ++ LBc) LB0 LM FRS B A1 m1' md1 HP1 INCL0) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUBb : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUBa b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
assert (LOCcs : forall a, 6434400 - 48 <= a < 6434400 - 48 + 8 -> hl_client_static A4H a).
{ intros a Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia].
clear SB1 SB2 SB3 UARC PEPC ERR.
pose proof (RTC_PEPC _ _ _ _ _ _ _ HP1) as PEPC. apply ro_C8_of_bytes_at in PEPC. unfold A_GOT_PEPC in PEPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(sp0 - 416, sp0); (tk, tk + 72); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in APt, HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. step. if_truex.
stepz. step. step. step. step. step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. stepz. stepz. stepz. step. step.
fold sh.
do 4 stepz. step. do 24 stepz. stepz. stepz. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX3 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX2 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP1 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (G3 : GA mc) by (eapply GA_outside; [exact G2 | exact MU | exact WM | pe_img_solve])
end.
clear HPX2 G2.

eapply evt_cut; [eapply USE; [exact LOC | unfold GLOBLOC_A; lia | lia | reflexivity | eassumption] |].
intros ms3 (m3 & a1x & a2x & a3x & a4x & -> & MU3 & WM3 & MI3 & LOC3).
replace (ret_pc (Z_to_bv 64 0x9325c)) with (Z_to_bv 64 0x9325c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA GLOBLOC_A 0) with GLOBLOC_A in LOC3 by reflexivity.
replace (usl_retA GLOBLOC_A) with LC_GLOBAL_A by reflexivity.
assert (HP2 : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B m2 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP1 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | exact MI1]. }
assert (HPX4 : heap_presx A4H xlocA L0 sp0 m m3)
by (eapply heap_presx_trans; [exact HPX3 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP2 MU3 WM3 SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]).
assert (G4 : GA m3) by (exact (GA_loc _ _ G3 MU3 WM3)).
assert (HP3 : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B m3 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP2 MU3); pe_fw_solve tk Fr sh INtk INF | exact WM3 | exact MI3]. }
clear HPX3 G3 HP2.
unfold LOCCELL_A, A_TP in MU3, LOC3.

eapply rw_cells_transport in TOK; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LCK; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply ro_cells_transport in PEPC; [| exact MU3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (ST3 : stk asegs m3 lo (sp0 + -416)).
{ eapply stk_transport; [exact ST1 | exact MU3 | exact WM3 |]. intros z Hz. left. cbn [outside]. lia. }
clear ST1 MU WM MU3 WM3 MI1 LOC.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(sp0 - 416, sp0); (tk, tk + 72)] m3) as MU.
assert (SHT3 : ro_cells asegs m3 (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP3 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
set (sht := tk / 8 + 2147450880) in *.
assert (SHTR : 2147450880 <= sht /\ sht + 9 <= 17594333495296) by (unfold sht; clear - Htlo Hthi ACR; Z.div_mod_to_equations; lia).
step. step. step.
rewrite (unsigned_lit (tk + 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (div8_add tk 32) by (clear - Htal; Z.div_mod_to_equations; lia). change (32 / 8) with 4.
replace (tk / 8 + 4 + 2147450880) with (sht + 4) by (unfold sht; lia).
step. rewrite ?sxb_zero. step. step. if_true.
stepz.
step. step. step.
rewrite (unsigned_lit (tk + 36)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (div8_add tk 36) by (clear - Htal; Z.div_mod_to_equations; lia). change (36 / 8) with 4.
replace (tk / 8 + 4 + 2147450880) with (sht + 4) by (unfold sht; lia).
step. rewrite ?sxb_zero. step. step. if_true.
step. stepz.
step.

unstash MODE.
assert (LRR : 0 <= lenr < 2^64 /\ (lenr = len \/ (lenr = LENW_C /\ 1 <= len))) by (destruct MODE as [_ [-> | (-> & L1 & _)]]; unfold LENW_C; lia).
assert (PLOC : len = 0 \/ (exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len <= Fh + fr_size kh - 8 /\ unpoisoned asegs m A_SB sb len)) by (exact (proj1 MODE)).
stash MODE.

assert (JOIN : forall (mJ : word -> option byte) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j1 j2 j3 j4 j5 j6 : list byte),
rw_cells asegs mJ tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells asegs mJ (sp0 + -416) [C8 (Z_to_bv 64 0); CB 256 j1; C8 (Z_to_bv 64 (sht + 4)); CB 8 j2; C8 (Z_to_bv 64 lenr); CB 8 j3; C8 (Z_to_bv 64 Fr); CB 4 j4; C4 (Z_to_bv 64 0);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mJ Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 128369); C8 (Z_to_bv 64 A_PE_ENTRY); CB 40 j5; C1 (Z_to_bv 8 1); CB 183 j6] ->
rw_cells asegs mJ sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243);
C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)] ->
rw_cells asegs mJ 6566352 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs mJ (6434400 - 164) [C4 errv1] ->
rw_cells asegs mJ (6434400 - 48) [C8 (Z_to_bv 64 GLOBLOC_A)] ->
stk asegs mJ lo (sp0 + -416) -> munch [(lo, sp0); (tk, tk + 72)] m3 mJ -> wmono asegs m3 mJ -> mem_inv asegs mJ ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (sp0 + -416)) gp (Z_to_bv 64 6434400) xt0 xt1 xt2 (Z_to_bv 64 sp0) (Z_to_bv 64 (sp0 + -416)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 sh) (Z_to_bv 64 tk) (Z_to_bv 64 (sht + 4)) (Z_to_bv 64 Fr) (Z_to_bv 64 (tk + 36)) (Z_to_bv 64 (tk + 32)) (Z_to_bv 64 Fr)
(Z_to_bv 64 2147450880) (Z_to_bv 64 LC_GLOBAL_A) (Z_to_bv 64 sb) xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x9337c) fc None mJ (seg_rom asegs))).
{ clear TOK FR FF1 FSH1 LCK ERR1 LOC3 ST3 MU WM MI3 SHT3 PEPC.
intros mJ xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 j1 j2 j3 j4 j5 j6 TOK FR FF1 FSH1 LCK ERR1 LOC3 ST3 MU WM MIJ.

assert (HPX5 : heap_presx A4H xlocA L0 sp0 m mJ)
by (eapply heap_presx_trans; [exact HPX4 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP3 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]).
assert (G5 : GA mJ) by (eapply GA_outside; [exact G4 | exact MU | exact WM | pe_img_solve]).
assert (HPJ : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B mJ md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP3 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | exact MIJ]. }
clear HPX4 G4 MU WM.
pose proof (wmono_refl asegs mJ) as WM. pose proof (munch_refl [(sp0 - 416, sp0)] mJ) as MU.

stepz. step. step.
evt_done5.
eapply (DUP) with (LB := TBS ++ LBc) (LM := LM) (FRS := (Fr, 2) :: FRS) (B := B) (lo := lo) (errv := errv1);
[ heap_nowA A4L HIx HPJ MU WM MIJ
| rewrite unsigned_lit by lia; exact ST3 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR1 | reflexivity
| rewrite unsigned_lit by lia; reflexivity | exact LMN | exact BM1 | ].
intros ms5 m5 md5 A5 rd errv5 RS5 VM5 ST5 HPR5 ERR5 OUT5. open_ret RS5.
rewrite (unsigned_lit (sp0 + -416)) in ST5, HPR5 by lia.

lazymatch type of HPR5 with heap_pres _ _ _ ?mc _ =>
assert (HPX6 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX5 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HPJ MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (G6 : GA mc) by (eapply GA_outside; [exact G5 | exact MU | exact WM | pe_img_solve])
end.
assert (SUBc : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM ++ fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply INCL0; exact Hb|]. apply in_or_app; right.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (HPX7 : heap_presx A4H xlocA L0 sp0 m m5).
{ eapply heap_presx_trans; [exact HPX6|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR5 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (G7 : GA m5) by (eapply GA_pres; [exact HPR5 | exact G6]).
clear HPX5 G5 HPX6 G6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR5.
clear MU WM MIJ ST3 ERR1 HPJ.

assert (STCJ : forall nl mdl, PE_STATIC_A HIx (PEF tk 0 0 len lenr sb (sp0 + -416) mdl mxd fl) (PEFA sp0 Fr LC_GLOBAL_A nl bsl dsl) lo).
{ intros nl mdl. unfold PE_STATIC_A, pe_geomA, LENR_OK; cbn [pf_spf pf_len pf_lenr pf_sb pf_md pf_mxd pf_fl pf_tk pa_sp0 pa_F].
repeat split; try (clear - LO LOS SPA HT SP62 SP0R PLEN LEN SB0 SBL LRR MXB HFal HF0 HFc Htal ACR; first [lia | Z.div_mod_to_equations; lia]). }
assert (EXIT : forall (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (BX : bud) (errvX : word) (eX : Z) (jsl jffx jshx : list byte)
(y1 u0' u1' u2' w0 w1 w2 w3 w4 w5 w6 w7 z4 z6 z7 z9 z10 z11 u3' u4' u5' u6' : word),
HEAPAx AX (TBS ++ LBc) LM ((Fr, 2) :: FRS) BX mX mdX ->
rw_cells asegs mX tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 eX); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells asegs mX (sp0 + -416) [CB 312 jsl] ->
rw_cells asegs mX (sp0 - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX Fr [CB 248 jffx] -> rw_cells asegs mX sh [CB 32 jshx] ->
stk asegs mX lo (sp0 + -416) -> rw_cells asegs mX (6434400 - 164) [C4 errvX] -> rw_cells asegs mX (6434400 - 48) [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA L0 sp0 m mX -> GA mX -> model_vm_only (cfg_model md) (cfg_model mdX) -> bB B <= bB BX -> bD B - M2D <= bD BX ->
AJ5 A4L HIx AX T mdX
(MS (mkR y1 (Z_to_bv 64 (sp0 + -416)) gp (Z_to_bv 64 6434400) u0' u1' u2' (Z_to_bv 64 sp0) (Z_to_bv 64 (sp0 + -416)) w0 w1 w2 w3 w4 w5 w6 w7
(Z_to_bv 64 sh) (Z_to_bv 64 0) z4 (Z_to_bv 64 Fr) z6 z7 (Z_to_bv 64 Fr) z9 z10 z11 u3' u4' u5' u6')
F (Z_to_bv 64 0x932bc) fc None mX (seg_rom asegs))).
{ clear TOK FR FF1 FSH1 LCK ERR5 LOC3 ST5.
intros mX mdX AX BX errvX eX jsl jffx jshx y1 u0' u1' u2' w0 w1 w2 w3 w4 w5 w6 w7 z4 z6 z7 z9 z10 z11 u3' u4' u5' u6' HPXh TOKX SLX SVX FFX FSHX STX ERRX LOCX HPXX GX VMX BBX BDX.
assert (INq0 : In (q, 32 * mxd) L0) by (unfold L0, LB0; left; reflexivity).
assert (INpbs : incl pbs L0) by (intros b Hb; unfold L0, LB0; right; apply in_or_app; left; apply in_or_app; left; exact Hb).
assert (AGq : agree_on asegs ((q, 32 * mxd) :: pbs) m mX).
{ eapply (agree_of_heap_presx asegs A4H); [exact HPXX | reflexivity |]. intros b [<- | Hb]; [exact INq0 | exact (INpbs b Hb)]. }
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
unstash PB. unstash TSK. unstash KR.
eapply (out_finish_AG HIx GA GA_outside (PEF tk 0 0 len lenr sb (sp0 + -416) (cfg_model mdX) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A 0 bsl dsl) LBc [] LM FRS m lo mX mdX md AX BX [] TBS 0
sv errvX T jsl [] jffx jshx) with (F0 := F) (fc0 := fc);
[ exact (STCJ 0 (cfg_model mdX)) | | | left; split; reflexivity | exact SLX | | exact SVX | exact FFX | exact FSHX | exact STX | exact ERRX | exact LOCX | | exact VMX | exact GX | | | | apply fsaved_refl | intros Hf; exact Hf | ].
- eapply (heapA_perm A4L HIx); [exact HPXh | cbn [app]; apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
- exists q, pb, 0, pbs, (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)), (TS (wz 0) (wz 0) (wz 0) (Z_to_bv 64 eX) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [rewrite ECC, app_nil_r; exact ETBS|]. split; [cbn [length pf_mxd]; rewrite repeat_length; lia|]. split; [cbn [pf_mxd pf_fl]; lia|].
split; [unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd pf_fl pf_tk]; exact TOKX|].
split; [eapply (pbuf_agree asegs); [exact PB | exact AGq | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AGq |]. exists q, (32 * mxd). split; [left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl) as Hi. cbn [length] in Hi. rewrite repeat_length in Hi. cbn [pf_mxd]. lia. }
split.
+ intros i li Hli Hile. assert (i = 0%nat) as -> by lia. cbn in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. destruct i as [|i]; [lia|]. change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. apply lvl_zero_clean.
- cbn [pf_spf pa_sp0]. replace (Z.to_nat (sp0 - 104 - (sp0 + -416 + 312))) with 0%nat by lia.
destruct SVX as [[_ SVB] SVW].
split; [split; [cbn; split; [reflexivity | exact I] |] |].
+ cbn [cells_bytes cbytes app]. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ SVB). lia.
+ cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia.
- cbn [pa_sp0]. eapply heap_presx_weaken; [exact HPXX | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0, LB0. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- cbn [pa_bslack app]. unfold K_free, K_exit in *. lia.
- cbn [pa_dslack]. lia.
- exact RAE.
- intros ms' md' A' P. apply KR. eapply pe_post_A_eq; [| | | | | | | exact P]; reflexivity. }
destruct OUT5 as [(Erd & Eerr & HP5) | (Hrd & (jd & DBLK) & HP5)].
-
subst rd errv5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (SHT5 : ro_cells asegs m5 sht
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP5 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
pose proof (OBL_SH_ERRNO _ _ _ _ _ _ _ HP5) as SHE. apply ro_C1_of_bytes_at in SHE. change (A_ERRNO / 8 + A_SB) with 2148255159 in SHE.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(sp0 - 416, sp0); (tk, tk + 72)] m5) as MU.
unfold ENOMEMv in ERR5. change (6434400 - 164) with 6434236 in ERR5.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. if_false.
step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x93394)) with (Z_to_bv 64 0x93394) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP.
step. step. step. rewrite ?sxb_zero. step. if_true.
step. norm_sx32. step. step. if_false.
step. step. rewrite ?sxb_zero. step. if_true.
step. step. step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXe : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX7 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP5 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (Ge : GA mc) by (eapply GA_outside; [exact G7 | exact MU | exact WM | pe_img_solve]);
assert (HPe : HEAPAx A5 (TBS ++ LBc) LM ((Fr, 2) :: FRS) (charge B 0 M2D) mc md5) by (heap_nowA A4L HIx HP5 MU WM MI5)
end.
lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval cbv in (length cs - 13)%nat in rewrite <- (firstn_skipn n cs) in FR end. cbn [firstn skipn] in FR.
lazymatch type of FR with rw_cells _ ?mm ?a (?x ++ ?y) => change (rw_cells asegs mm a ([] ++ x ++ y)) in FR end.
apply rw_cells_merge in FR. cbn [app] in FR.
lazymatch type of FR with rw_cells _ _ _ (CB ?n ?b :: ?post) => let v := eval vm_compute in n in change n with v in FR; change (CB v b :: post) with ([CB v b] ++ post) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [SL SV]. cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 312) with 312 in SV.
replace (sp0 + -416 + 312) with (sp0 - 104) in SV by lia.
lazymatch type of FF1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FF1 end. apply rw_cells_merge in FF1. cbn [app] in FF1.
lazymatch type of FF1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FF1 end.
lazymatch type of FSH1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FSH1 end. apply rw_cells_merge in FSH1. cbn [app] in FSH1.
lazymatch type of FSH1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FSH1 end.
evt_done5.
eapply (EXIT _ md5 A5 (charge B 0 M2D) (Z_to_bv 64 12) 16); [exact HPe | exact TOK | exact SL | exact SV | exact FF1 | exact FSH1 | exact ST5 | exact ERR5 | exact LOC3 | exact HPXe | exact Ge
| eapply model_vm_only_trans; [exact VM1 | exact VM5] | cbn [bB charge]; lia | cbn [bD charge]; lia].
-
assert (INd : In (rd, 48) ((TBS ++ LBc) ++ (rd, 48) :: LM)) by (apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd 48 HP5 INd) as (_ & Hdal & Hdlo & Hdhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ rd 48 HP5 INd) as Himg_d. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_d.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(sp0 - 416, sp0)] m5) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. if_truex.
step. step. step. step. step.
evt_done5.
eapply (NEWL) with (LB := TBS ++ LBc) (LM := (rd, 48) :: LM) (FRS := (Fr, 2) :: FRS) (B := charge B 0 M2D) (lo := lo) (d := rd) (junk := jd) (errv := errv5);
[ exact HP5 | left; reflexivity | exact DBLK | exact LCK | rewrite unsigned_lit by lia; exact ST5 | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR5 | reflexivity
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms6 m6 rn jn RS6 ST6 HPR6 DBLK6 LCK6 ERR6 HP6 Hrn. open_ret RS6.
rewrite (unsigned_lit (sp0 + -416)) in ST6, HPR6 by lia.
rewrite lb_remove_head in HPR6.
assert (HPX8 : heap_presx A4H xlocA L0 sp0 m m6).
{ eapply heap_presx_trans; [exact HPX7|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR6 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (G8 : GA m6) by (eapply GA_pres; [exact HPR6 | exact G7]).
clear HPX7 G7.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR6.
clear MU WM MI5 ST5 ERR5 DBLK LCK LCK6.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI6. change (hl_segs A4L) with asegs in MI6.
pose proof (wmono_refl asegs m6) as WM. pose proof (munch_refl [(sp0 - 416, sp0); (tk, tk + 72)] m6) as MU.
assert (SHT6 : ro_cells asegs m6 sht
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP6 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
assert (INtk6 : In (tk, 72) ((TBS ++ LBc) ++ (rd, 48) :: LM)) by (apply in_or_app; left; exact INtkB).
assert (SUBd : forall b, In b L0 -> In b ((TBS ++ LBc) ++ (rd, 48) :: LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUBb b Hb) as [H | H]; [left | right; exact H]. apply in_app_or in H as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]. }
reenterA asegs A4L HIx asegs_wx HP6.
destruct Hrn as [-> | ->].
2:{
step. if_false. step.
step. step. rewrite ?sxb_zero. step. if_true.
step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXf : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX8 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]);
assert (Gf : GA mc) by (eapply GA_outside; [exact G8 | exact MU | exact WM | pe_img_solve])
end.
evt_done5.
eapply (FREEL) with (LB := TBS ++ LBc) (LM := (rd, 48) :: LM) (FRS := (Fr, 2) :: FRS) (B := charge B 0 M2D) (d := rd) (n := 48) (lo := lo) (errv := errv5);
[ heap_nowA A4L HIx HP6 MU WM MI6 | left; reflexivity | rewrite unsigned_lit by lia; exact ST6 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR6 | reflexivity | rewrite unsigned_lit by lia; reflexivity | ].
intros ms9 m9 md9 A9 r9 RS9 VM9 ST9 HPR9 ERR9 HP9. open_ret RS9.
rewrite (unsigned_lit (sp0 + -416)) in ST9, HPR9 by lia.
rewrite lb_remove_head in HPR9, HP9.
assert (HPXg : heap_presx A4H xlocA L0 sp0 m m9).
{ eapply heap_presx_trans; [exact HPXf|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR9 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (Gg : GA m9) by (eapply GA_pres; [exact HPR9 | exact Gf]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR9.
clear MU WM MI6.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP9) as MI9. change (hl_segs A4L) with asegs in MI9.
pose proof (wmono_refl asegs m9) as WM. pose proof (munch_refl [(sp0 - 416, sp0)] m9) as MU.
reenterA asegs A4L HIx asegs_wx HP9.
step. step.
lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval cbv in (length cs - 13)%nat in rewrite <- (firstn_skipn n cs) in FR end. cbn [firstn skipn] in FR.
lazymatch type of FR with rw_cells _ ?mm ?a (?x ++ ?y) => change (rw_cells asegs mm a ([] ++ x ++ y)) in FR end.
apply rw_cells_merge in FR. cbn [app] in FR.
lazymatch type of FR with rw_cells _ _ _ (CB ?n ?b :: ?post) => let v := eval vm_compute in n in change n with v in FR; change (CB v b :: post) with ([CB v b] ++ post) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [SL SV]. cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 312) with 312 in SV.
replace (sp0 + -416 + 312) with (sp0 - 104) in SV by lia.
lazymatch type of FF1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FF1 end. apply rw_cells_merge in FF1. cbn [app] in FF1.
lazymatch type of FF1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FF1 end.
lazymatch type of FSH1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FSH1 end. apply rw_cells_merge in FSH1. cbn [app] in FSH1.
lazymatch type of FSH1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FSH1 end.
evt_done5.
eapply (EXIT _ md9 A9 (charge B 0 M2D) errv5 16); [exact HP9 | exact TOK | exact SL | exact SV | exact FF1 | exact FSH1 | exact ST9 | exact ERR9 | exact LOC3 | exact HPXg | exact Gg
| eapply model_vm_only_trans; [exact VM1 | eapply model_vm_only_trans; [exact VM5 | exact VM9]] | cbn [bB charge]; lia | cbn [bD charge]; lia]. }
step. if_truex.
stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. stepz. step. stepz. stepz. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX9 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX8 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]);
assert (G9 : GA mc) by (eapply GA_outside; [exact G8 | exact MU | exact WM | pe_img_solve]);
assert (HP6' : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mc md5) by (heap_nowA A4L HIx HP6 MU WM MI6)
end.
eapply evt_cut; [eapply USE; [exact LOC3 | unfold GLOBLOC_A; lia | split; [lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi; lia] | reflexivity | eassumption] |].
intros ms7 (mu7 & a1y & a2y & a3y & a4y & -> & MU7 & WM7 & MI7 & LOC7).
replace (ret_pc (Z_to_bv 64 0x934f0)) with (Z_to_bv 64 0x934f0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA GLOBLOC_A rd) with rd in LOC7
by (unfold usl_newA; destruct (Z.eqb_spec rd 0); [lia|]; destruct (Z.eqb_spec rd LC_GLOBAL_A); [unfold LC_GLOBAL_A in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi; lia | reflexivity]).
assert (HPX10 : heap_presx A4H xlocA L0 sp0 m mu7)
by (eapply heap_presx_trans; [exact HPX9 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6' MU7 WM7 SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]).
assert (G10 : GA mu7) by (exact (GA_loc _ _ G9 MU7 WM7)).
assert (HP7 : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mu7 md5).
{ eapply (heapA_client_frame A4L HIx); [exact HP6' | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP6' MU7); pe_fw_solve tk Fr sh INtk6 INF | exact WM7 | exact MI7]. }
clear HPX8 G8 HPX9 G9 HP6'.
unfold LOCCELL_A, A_TP in MU7, LOC7.
eapply rw_cells_transport in TOK; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR6; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in DBLK6; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (ST7 : stk asegs mu7 lo (sp0 + -416)).
{ eapply stk_transport; [exact ST6 | exact MU7 | exact WM7 |]. intros z Hz. left. cbn [outside]. lia. }
clear ST6 MU WM MU7 WM7 MI6 LOC3.
pose proof (wmono_refl asegs mu7) as WM. pose proof (munch_refl [(sp0 - 416, sp0)] mu7) as MU.
stepz.
step. step. step. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz.
step. step. stepz.
step. step. step. step. step. step. step. stepz. step. stepz. step. step. stepz.
stepz. stepz. stepz. stepz. stepz. stepz. step. step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX11 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX10 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP7 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]);
assert (G11 : GA mc) by (eapply GA_outside; [exact G10 | exact MU | exact WM | pe_img_solve]);
assert (HP8 : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mc md5) by (heap_nowA A4L HIx HP7 MU WM MI7)
end.
clear HPX10 G10.

rewrite ?(unsigned_lit (tk + 20)), ?(unsigned_lit (tk + 32)), ?(unsigned_lit (tk + 56)), ?(unsigned_lit (tk + 64)) by lia.
rewrite ?(unsigned_lit (tk + 20)), ?(unsigned_lit (tk + 32)), ?(unsigned_lit (tk + 56)), ?(unsigned_lit (tk + 64)) in FR by lia.
rewrite ?Z.shiftr_div_pow2 by lia. rewrite ?Z.shiftr_div_pow2 in FR by lia. change (2^3) with 8 in *.
rewrite ?(div8_add tk 20), ?(div8_add tk 56), ?(div8_add tk 64) by (clear - Htal; Z.div_mod_to_equations; lia).
rewrite ?(div8_add tk 20), ?(div8_add tk 56), ?(div8_add tk 64) in FR by (clear - Htal; Z.div_mod_to_equations; lia).
change (20 / 8) with 2 in *. change (56 / 8) with 7 in *. change (64 / 8) with 8 in *.
rewrite ?land7_mod8 by lia. rewrite ?land7_mod8 in FR by lia.
replace (sht + 4) with (tk / 8 + SB4) by (unfold sht, SB4; lia).
replace (tk / 8 + 2 + 2147450880) with (tk / 8 + SB2) by (unfold SB2; lia).
replace (tk / 8 + 8 + 2147450880) with (tk / 8 + SB8) by (unfold SB8; lia).
replace (Z_to_bv 64 sb) with (Z_to_bv 64 (sb + 0)) by (f_equal; lia).
replace (sht + 4) with (tk / 8 + 4 + A_SB) in FR by (unfold sht, A_SB; lia).
replace (tk / 8 + 2 + 2147450880) with (tk / 8 + 2 + A_SB) in FR by (unfold A_SB; lia).
replace (tk / 8 + 7 + 2147450880) with (tk / 8 + 7 + A_SB) in FR by (unfold A_SB; lia).
replace (tk / 8 + 8 + 2147450880) with (tk / 8 + 8 + A_SB) in FR by (unfold A_SB; lia).
evt_done5. unstash KL.
lazymatch type of FR with rw_cells _ _ _ (_ :: CB 16 ?J16 :: _) =>
lazymatch type of FF1 with rw_cells _ _ _ [C8 ?h0; C8 ?h1; C8 ?h2; CB 40 ?J5; _; CB 183 ?J6] =>
eapply (KL rd (sp0 + -416) Fr m8 md5 A5 (charge B 0 M2D) (Z_to_bv 64 0)
(PEJA (le8 (Z_to_bv 64 0)) (le_bytes_to_word (firstn 8 J16)) (le_bytes_to_word (skipn 8 J16)) (Z_to_bv 64 0) j3 j4 [] (le8 h0 ++ le8 h1 ++ le8 h2) J5 J6) errv5)
end end.
+
unfold PE_STATIC_A, pe_geomA, LENR_OK; cbn [pf_spf pf_len pf_lenr pf_sb pf_md pf_mxd pf_fl pf_tk pa_sp0 pa_F].
repeat split; try (clear - LO LOS SPA HT SP62 SP0R PLEN LEN SB0 SBL LRR MXB HFal HF0 HFc Htal ACR; first [lia | Z.div_mod_to_equations; lia]).
+
assert (INq0 : In (q, 32 * mxd) L0) by (unfold L0, LB0; left; reflexivity).
assert (INpbs : incl pbs L0) by (intros b Hb; unfold L0, LB0; right; apply in_or_app; left; apply in_or_app; left; exact Hb).
assert (AGq : agree_on asegs ((q, 32 * mxd) :: pbs) m m8).
{ eapply (agree_of_heap_presx asegs A4H); [exact HPX11 | reflexivity |]. intros b [<- | Hb]; [exact INq0 | exact (INpbs b Hb)]. }
unstash PB. unstash TSK. unstash STR.
split.
* unfold PE_CORE_A, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [cbn [length]; rewrite repeat_length; lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote Z.of_nat]; exact TOK|].
split; [eapply (pbuf_agree asegs); [exact PB | exact AGq | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AGq |]. exists q, (32 * mxd). split; [left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl) as Hi. cbn [length] in Hi. rewrite repeat_length in Hi. lia. }

unfold pe_frameA; cbn [pf_spf pf_tk pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc].
lazymatch type of FR with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 39 cs) in FR end. cbn [firstn skipn] in FR.
apply (proj1 (rw_cells_app asegs m8 _ _ _)) in FR. destruct FR as [SL SV].
lazymatch type of SV with rw_cells _ _ (_ + Z.of_nat ?n) _ => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in SV end.
replace (sp0 + -416 + 312) with (sp0 - 104) in SV by lia.
pose proof SL as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS.
pose proof FF1 as [[WFF _] _]. cbn [cells_wf cell_wf] in WFF.
lazymatch type of SL with rw_cells _ _ _ (_ :: CB 16 ?J :: _) => set (J16 := J) in * end.
assert (LJ16 : length J16 = 16%nat) by (clear - WFS; tauto).
assert (Lj3 : length j3 = 8%nat) by (clear - WFS; tauto).
assert (Lj4 : length j4 = 4%nat) by (clear - WFS; tauto).
split.
{ eapply rw_cells_recast; [exact SL | | | ].
- unfold pe_slotsA; cbn [cells_wf cell_wf pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pf_tk pf_lenr pa_F pa_newloc pa_oldloc]. rewrite length_le8. clear - LJ16 Lj3 Lj4. tauto.
- unfold pe_slotsA; cbn [cells_bytes cbytes app pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pf_tk pf_lenr pa_F pa_newloc pa_oldloc].
rewrite !Q8l1.Mq2.le8_of_bytes by (rewrite ?firstn_length, ?skipn_length, LJ16; reflexivity).
f_equal. rewrite app_assoc, firstn_skipn. reflexivity.
- reflexivity. }
split.
{
cbn [pj_gap]. replace (Z.to_nat (sp0 - 104 - (sp0 + -416 + 312))) with 0%nat by lia.
destruct SV as [[_ SVB] SVW].
split; [split; [cbn; split; [reflexivity | exact I] |] |].
- cbn [cells_bytes cbytes app]. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ SVB). lia.
- cbn [cells_size csize Nat.add Z.of_nat]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
split; [exact SV|].
split.
{ eapply rw_cells_recast; [exact FF1 | | | ].
- unfold ff_cellsA; cbn [cells_wf cell_wf pj_fhd pj_f1 pj_f2]. rewrite !length_app, !length_le8. clear - WFF. tauto.
- unfold ff_cellsA; cbn [cells_bytes cbytes app pj_fhd pj_f1 pj_f2]. rewrite <- !app_assoc. reflexivity.
- reflexivity. }
{ eapply rw_cells_recast; [exact FSH1 | | | ].
- unfold ffsh_cells, FSH0. cbn [map cells_wf cell_wf]. repeat split.
- unfold ffsh_cells, FSH0. cbn [map cells_bytes cbytes app repeat]. reflexivity.
- reflexivity. }
*
unfold PE_REST_A, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj t_objs t_objbs ts_choff pf_len pf_tk pf_spf pf_sb pf_md pf_mxd pf_fl pa_sp0 pa_F pa_bslack pa_dslack].
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
split.
{ eapply (heapA_perm A4L HIx); [exact HP8 | | apply Permutation_refl | apply Permutation_refl].
unfold pe_blocksA, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_tk pf_mxd]. rewrite ECC, ETBS. perm. }
split.
{ intros i li Hli. unfold lvl_cur.
destruct i as [|i].
- cbn in Hli. injection Hli as <-. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_reset Nat.ltb Nat.eqb Nat.leb].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|]. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
- change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_zero].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|].
replace (S i <? 0)%nat with false by reflexivity. replace (S i =? 0)%nat with false by reflexivity. apply lvl_zero_clean. }
split; [reflexivity|].
split; [exact ST7|]. split; [exact ERR6|].
split.
{ destruct PLOC as [Z0 | PL].
- destruct payload; [| cbn in PLEN; lia]. apply bytes_at_nil. lia.
- eapply (heap_presx_bytes_at A4H); [exact HPX11 | exact STR |]. rewrite PLEN.
destruct PL as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)].
+ destruct bb as [ba bn]. eapply client_rangex_block; [unfold L0, LB0; apply in_or_app; left; right; apply in_or_app; right; exact Hbb | exact Hb1 | exact Hb2].
+ eapply client_rangex_block; [unfold L0; apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFh | exact HF1 | lia]. }
split; [exact PLEN|].
split.
{ assert (PL0 : len = 0 \/ payload_locA (PEF tk 0 0 len lenr sb (sp0 + -416) (cfg_model md5) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A rd bsl dsl) LBc FRS m).
{ destruct PLOC as [Z0 | PL]; [left; exact Z0 | right]. unfold payload_locA; cbn [pf_sb pf_len]. exact PL. }
exact (payload_locA_presx HIx xlocA (PEF tk 0 0 len lenr sb (sp0 + -416) (cfg_model md5) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A rd bsl dsl) LBc FRS _ _ _ _ _ _ _ LB0 sp0 m m8 HP (incl_refl _) HPX11 PL0). }
split; [apply heap_presx_refl|]. split; [apply model_vm_only_refl|].
split; [exact G11|].
unfold PE_BUD, tstate_blocks; cbn [t_pbs t_objbs t_levels pa_bslack pa_dslack bB bD charge]. rewrite ECC, !app_nil_r.
rewrite ETBS in BB. cbn [app length] in BB. unfold K_free, K_exit in *. rewrite ?Nat2Z.inj_succ in BB. lia.
+ eapply model_vm_only_trans; [exact VM1 | exact VM5].
+ eapply heap_presx_weaken; [exact HPX11 | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0, LB0. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
+ eapply (agree_of_heap_presx asegs A4H); [exact HPX11 | reflexivity |]. intros b Hb. unfold L0, LB0. apply in_or_app; left. right. apply in_or_app; left. exact Hb.
+ exact LOC7.
+ unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi. lia.
+ cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
}

unstash MODE. destruct MODE as [_ [Elr | (Elr & LEN1 & (str0 & Ep & NONUL) & SLK & PAD & SLOC)]].
-
subst lenr. if_truex. stepz. step. if_truex.
eapply JOIN; [exact TOK | exact FR | exact FF1 | exact FSH1 | exact LCK | exact ERR1 | exact LOC3 | exact ST3
| eapply munch_weaken; [| exact MU]; intros z Hz; cbn [outside] in Hz |- *; lia | exact WM | eassumption].
-
subst lenr. replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) in * by (apply bv_eq; reflexivity).
if_lit true. stepz. step. if_lit false. step. step.
assert (ELEN : Z.of_nat (length str0) + 1 = len) by (subst payload; rewrite length_app in PLEN; cbn [length] in PLEN; lia).
assert (HI47 : sb + len + Z.of_nat (length slack) <= alloc_ceiling).
{ destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)].
- destruct bb as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; right; exact Hbb)) as (_ & _ & _ & Hhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFh) as (_ & _ & _ & Hhi & _). lia. }
unstash STR.
assert (CAT : bytes_at asegs m sb (str0 ++ Z_to_bv 8 0 :: slack)).
{ assert (C0 : bytes_at asegs m sb (payload ++ slack)) by (apply bytes_at_app; split; [exact STR | rewrite PLEN; exact SLK]).
subst payload. rewrite <- app_assoc in C0. cbn [app] in C0. exact C0. }
assert (LCAT : Z.of_nat (length (str0 ++ Z_to_bv 8 0 :: slack)) = len + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXc : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX4 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP3 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (HPc : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B mc md1)
by (eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP3 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | eassumption]);
assert (CATc : bytes_at asegs mc sb (str0 ++ Z_to_bv 8 0 :: slack));
[ eapply (heap_presx_bytes_at A4H); [exact HPXc | exact CAT |]; rewrite LCAT;
destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)];
[ destruct bb as [ba bn]; eapply client_rangex_block; [unfold L0, LB0; apply in_or_app; left; right; apply in_or_app; right; exact Hbb | cbn [blk_addr blk_size fst snd] in *; lia | cbn [blk_addr blk_size fst snd] in *; lia]
| eapply client_rangex_block; [unfold L0; apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFh | exact HF1 | lia] ] |];
assert (UPc : unpoisoned asegs mc A_SB sb len);
[ destruct PLOC as [Z0 | [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]]; [lia | |];
[ destruct bb as [ba bn]; cbn [blk_addr blk_size fst snd] in Hb1, Hb2;
eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ ba bn sb len HPc); [apply in_or_app; right; exact Hbb | exact Hb1 | exact Hb2 | lia]
| exact (unpoisoned_presx_frame HIx xlocA _ _ _ _ _ _ _ LB0 sp0 m mc Fh kh sb len HP HFh HF1 HF2 UPS HPXc) ] |];
assert (RTc : asan_rt_ok mc) by (exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc))
end.
assert (AM : 64 < len -> app_mem sb len).
{ intros _. unfold app_mem, A_HMB. destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)].
- destruct bb as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; right; exact Hbb)) as AP. cbn [hl_sb A4L] in AP. unfold A_SB in *.
split; [lia|]. destruct AP as [AP | AP]; [left; lia | right; lia].
- pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFh) as AP. cbn [hl_sb A4L] in AP. unfold A_SB in *.
split; [lia|]. destruct AP as [AP | AP]; [left; lia | right; lia]. }
eapply (ISTRLEN) with (a := sb) (lo := lo) (s := str0) (slack := slack);
[ rewrite ELEN; exact UPc | exact RTc | exact SB0 | unfold alloc_ceiling, sp_window_lo, stack_max_size in HI47; lia | lia | rewrite ELEN; exact AM
| left; lia | reflexivity | exact NONUL | exact CATc | replace (sb + Z.of_nat (length str0) + 1) with (sb + len) by lia; exact PAD
| rewrite unsigned_lit by lia; eassumption | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| eassumption | rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mS MUS WMS MIS STS.
rewrite (unsigned_lit (sp0 + -416)) in MUS, STS by lia.
replace (ret_pc (Z_to_bv 64 0x93374)) with (Z_to_bv 64 0x93374) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply rw_cells_transport in TOK; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LCK; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LOC3; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (MUJ : munch [(lo, sp0); (tk, tk + 72)] m3 mS).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUS]]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO LOS; lia. }
pose proof (wmono_trans _ _ _ _ WM WMS) as WMJ.
clear MU WM. pose proof (wmono_refl asegs mS) as WM. pose proof (munch_refl [] mS) as MU.
step.
rewrite (unsigned_lit (Z.of_nat (length str0))) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
step. if_false.
eapply JOIN; [exact TOK | exact FR | exact FF1 | exact FSH1 | exact LCK | exact ERR1 | exact LOC3 | exact STS | exact MUJ | exact WMJ | exact MIS].
Qed.
End PeSEntry.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlCE.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhHQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Ki.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Ki. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql4f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql4f.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGdd.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcmL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcmL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV7s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV7s.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdGy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdGy.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ2r.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ2r.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYZ0.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtyQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtyQ.Mqb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc5u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_ISTRLEN : Z := 0x4fd28.
Definition A_PE_ENTRY : Z := 0x93a24.
Definition A_GOT_PEPC : Z := 0xe8e88.
Definition PE_STK_A : Z := 432 + 12288.

Section PeSEntryB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_loc : forall m m', GA m -> munch [(LOCCELL_A, LOCCELL_A + 8)] m m' -> wmono asegs m m' -> GA m'.
Notation HEAPAx := (HEAPA A4L HIx).
Definition rtc_pepc_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_PEPC (le8 (Z_to_bv 64 A_PE_ENTRY)).
Hypothesis RTC_PEPC : rtc_pepc_stmt.

Definition heapA_errno_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> exists errv, rw_cells asegs m A_ERRNO [C4 errv].
Hypothesis OBL_ERRNO : heapA_errno_stmt.

Lemma presx_private : forall A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))
\/ (LOCCELL_A <= fst iv /\ snd iv <= LOCCELL_A + 8)) W ->
heap_presx A4H xlocA L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. clear MU.
induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW].
cbn [fst snd] in H1.
assert (OLD : ((alloc_ceiling <= lo /\ hi <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= lo /\ hi <= a + n)
\/ (forall x, lo <= x < hi -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= lo /\ hi <= F + fr_size k) \/ (shad A4L F <= lo /\ hi <= shad A4L F + fr_shadow_len k)))) -> ~ (lo <= a < hi)).
{ intros H1'. pose proof (client_outsideF HIx A LBall LM FR B L0 m md [(lo, hi)] SP HP Hsub HSP
ltac:(apply Forall_cons; [exact H1' | apply Forall_nil]) a Ha (client_addrx_addr A4H _ _ _ _ Hc)) as Ho.
cbn [outside] in Ho. exact (proj1 Ho). }
destruct H1 as [H1 | [H1 | [H1 | H1]]]; [apply OLD; left; exact H1 | apply OLD; right; left; exact H1 | apply OLD; right; right; right; exact H1 |].
intros Hin. pose proof alloc_ceiling_range as ACR. unfold LOCCELL_A, A_TP in H1.
destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- lia.
- apply Hx. right. unfold LOCCELL_A, A_TP. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr. destruct (Hsub _ Hb) as [Hb' | Hb'].
+ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP Hb') as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr. Z.div_mod_to_equations. lia.
Qed.

Definition sh_errno_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m (A_ERRNO / 8 + A_SB) [Z_to_bv 8 0].
Hypothesis OBL_SH_ERRNO : sh_errno_stmt.
Hypothesis USE : uselocale_A_stmt.
Hypothesis ERRNOL : errno_location_A_stmt.
Hypothesis DUP : duplocale_A_stmt HIx.
Hypothesis NEWL : newlocale_A_stmt HIx.
Hypothesis FREEL : freelocale_A_stmt HIx.

Definition istrlen_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a lo : Z) (s slack : list byte) (Q : machine_state -> Prop),
unpoisoned asegs m A_SB a (Z.of_nat (length s) + 1) -> asan_rt_ok m ->
0 <= a -> a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= 2^47 -> Z.of_nat (length s) + 1 < 2^40 ->
(64 < Z.of_nat (length s) + 1 -> app_mem a (Z.of_nat (length s) + 1)) ->
(a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= a) ->
a0 = Z_to_bv 64 a -> ~ In (Z_to_bv 8 0) s ->
bytes_at asegs m a (s ++ Z_to_bv 8 0 :: slack) -> (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length s))) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ISTRLEN) fc None m (seg_rom asegs)).
Hypothesis ISTRLEN : istrlen_spec_U.

Definition pe_arg_okA (m : word -> option byte) (LBc : list blk) (FRS : list frame) (sb len lenr : Z) (payload slack : list byte) : Prop :=
(len = 0 \/ (exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len <= Fh + fr_size kh - 8 /\ unpoisoned asegs m A_SB sb len)) /\
(lenr = len \/
(lenr = 2^64 - 1 /\ 1 <= len /\ (exists str0, payload = str0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) str0) /\
bytes_at asegs m (sb + len) slack /\ (- (sb + len)) mod 8 <= Z.of_nat (length slack) /\
((exists b, In b LBc /\ blk_addr b <= sb /\ sb + len + Z.of_nat (length slack) <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len + Z.of_nat (length slack) <= Fh + fr_size kh - 8)))).

Lemma pe_post_A_eq : forall pf pa pf' pa' sv F fc md LBc LM FRS me lo ms' md' A',
pf_tk pf = pf_tk pf' -> pf_mxd pf = pf_mxd pf' -> pf_fl pf = pf_fl pf' -> pf_len pf = pf_len pf' ->
pa_sp0 pa = pa_sp0 pa' -> pa_bslack pa = pa_bslack pa' -> pa_dslack pa = pa_dslack pa' ->
pe_post_A HIx GA pf pa sv F fc md LBc LM FRS me lo ms' md' A' -> pe_post_A HIx GA pf' pa' sv F fc md LBc LM FRS me lo ms' md' A'.
Proof.
intros pf pa pf' pa' sv F fc md LBc LM FRS me lo ms' md' A' E1 E2 E3 E7 E4 E5 E6 P. unfold pe_post_A in *. rewrite <- E1, <- E2, <- E3, <- E4, <- E5, <- E6, <- E7. exact P.
Qed.

Ltac pe_fw_solve tk Fr sh INtk INF :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; split; [exact INtk | cbn [fst snd]; lia]
| right; right; right; left; exists Fr, 2; split; [exact INF|]; left; cbn [fst snd]; rewrite fr_size_2; lia
| right; right; right; left; exists Fr, 2; split; [exact INF|]; right; cbn [fst snd]; unfold sh, shad; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; unfold A_SB; lia
| right; right; right; right; cbn [fst snd]; intros x Hx; unfold LOCCELL_A, A_TP in Hx; cbn [hl_client_static A4H]; unfold a4_client_static; lia ] | ]);
apply Forall_nil.
Ltac pe_px_solve1 tk INtk NTK :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; (split; [exact INtk|]); (split; [exact NTK|]); cbn [fst snd]; lia
| right; right; right; cbn [fst snd]; unfold LOCCELL_A, A_TP; lia ] | ]);
apply Forall_nil.
Ltac pe_px_solve tk Fr sh INtk NTK INF OFF OFS :=
repeat (apply Forall_cons;
[ first [ left; cbn [fst snd]; lia
| right; left; exists tk, 72; (split; [exact INtk|]); (split; [exact NTK|]); cbn [fst snd]; lia
| right; right; left; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]); left; cbn [fst snd]; rewrite fr_size_2; lia
| right; right; left; exists Fr, 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]); right; cbn [fst snd]; unfold sh, shad; cbn [hl_sb A4L]; rewrite fr_shadow_len_2; unfold A_SB; lia
| right; right; right; cbn [fst snd]; unfold LOCCELL_A, A_TP; lia ] | ]);
apply Forall_nil.
Ltac if_lit b :=
lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (vm_compute; reflexivity); cbv iota end.
Ltac pe_img_solve := repeat (apply Forall_cons; [cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; lia | ]); apply Forall_nil.
Definition seg_entry_B0_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (TBS LBc LM : list blk) (FRS : list frame) (B : bud) (tk sb len lenr lo bsl dsl sp0 : Z) (payload slack : list byte) (errv : word) (mxd fl q pb : Z) (pbs : list blk),
HEAPAx A (TBS ++ LBc) LM FRS B m md ->

TBS = [(tk, 72); (q, 32 * mxd)] ++ pbs -> (1 <= mxd <= 32 /\ 0 <= fl < 2^32) ->
rw_cells asegs m tk (tok_cells_g mxd fl pb 0 q (TS (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (Z_to_bv 8 0))) ->
pbuf asegs m pbs pb -> pb <> 0 ->
tstack asegs m q (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)) ->
bytes_at asegs m sb payload -> Z.of_nat (length payload) = len -> 0 <= len < 2^26 ->
pe_arg_okA m LBc FRS sb len lenr payload slack -> 0 <= sb -> sb + len < 2^63 ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
rw_cells asegs m LOCALE_LOCK_A [C4 (Z_to_bv 64 0)] -> GA m ->
sp = Z_to_bv 64 sp0 ->
stk asegs m lo sp0 -> alloc_ceiling <= lo -> lo <= sp0 - PE_STK_A ->
sp0 mod 32 = 16 -> sp0 + 32 <= hiA_top A4L HIx -> sp0 < 2^62 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 tk -> a1 = Z_to_bv 64 sb -> a2 = Z_to_bv 64 lenr ->
Z.of_nat (length LM) < 8 -> Z.of_nat (length FRS) + 2 < 4096 -> M2D <= bD B ->
K_free * Z.of_nat (length TBS) + K_exit + bsl <= bB B -> M2D + dsl <= bD B -> 0 <= bsl ->
let sv := PES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 in

(forall (newl spf Ff : Z) (m1 : word -> option byte) (md1 : config) (A1 : ASA A4L HIx) (B1 : bud)
(nb : word) (pj : pe_junkA) (errv1 : word) (gp' t0' a0' a1' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' : word),
let pf := PEF tk 0 0 len lenr sb spf (cfg_model md1) mxd fl in
let pa := PEFA (sp0) Ff LC_GLOBAL_A newl bsl dsl in
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LBc ((newl, 48) :: LM) FRS payload m1 lo m1 md1 A1 B1 (ts_init mxd pb pbs) (Z_to_bv 8 1) nb pj sv errv1 ->
model_vm_only (cfg_model md) (cfg_model md1) ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (sp0) m m1 ->
agree_on asegs pbs m m1 ->
rw_cells asegs m1 LOCCELL_A [C8 (Z_to_bv 64 newl)] -> 0 < newl < 2^64 ->
bB B <= bB B1 -> bD B - M2D <= bD B1 ->
AJ5 A4L HIx A1 T md1 (pe_msA asegs pf pa APE_LOOP 0 gp' t0' a0' a1' (Z_to_bv 64 (tk + 36)) a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F fc m1)) ->

(forall ms' md' A', pe_post_A HIx GA (PEF tk 0 0 len lenr sb 0 (cfg_model md) mxd fl) (PEFA (sp0) 0 0 0 bsl dsl) sv F fc md LBc LM FRS m lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_PE_ENTRY) fc None m (seg_rom asegs)).

Lemma seg_entry_B0 : seg_entry_B0_stmt.
Proof.
cbv delta [seg_entry_B0_stmt]. intros until pbs. intros HP ETBS MXB TOK PB Hpb TSK STR PLEN LEN MODE SB0 SBL LOC LCK G ESP ST LO LOS SPA HT SP62 ERR TP RAE A0 A1 A2 LMN FRN BM1 BB BD BSL sv KL KR.
unfold PE_STK_A in LOS.
subst a0 a1 a2 tp sp.
assert (INtk : In (tk, 72) ((TBS ++ LBc) ++ LM)) by (apply in_or_app; left; rewrite ETBS; left; reflexivity).
assert (INtkB : In (tk, 72) (TBS ++ LBc)) by (rewrite ETBS; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4.
pose proof (RTC_PEPC _ _ _ _ _ _ _ HP) as PEPC. apply ro_C8_of_bytes_at in PEPC. unfold A_GOT_PEPC in PEPC.
a4l.
assert (SP0R : 0 <= sp0 < 2^64) by lia.

set (LB0 := (q, 32 * mxd) :: pbs ++ LBc).
set (L0 := LB0 ++ LM ++ fr_ivs A4L FRS).
assert (INCL0 : incl LB0 (TBS ++ LBc)) by (unfold LB0; rewrite ETBS; intros b Hb; right; exact Hb).
assert (SUBa : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM) \/ In b (fr_ivs A4L FRS)).
{ intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; apply INCL0; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]. }
assert (NTK : ~ In (tk, 72) L0).
{ intros Hin. unfold L0 in Hin. apply in_app_or in Hin as [Hin | Hin].
- pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite ETBS in ND. cbn [app map blk_addr fst] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. unfold LB0 in Hin.
destruct Hin as [E | Hin]; [left; injection E; intros; lia | right; rewrite map_app; apply in_or_app; left; exact (in_map blk_addr _ _ Hin)].
- apply in_app_or in Hin as [Hin | Hin]; [| exact (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INtk Hin)].
exact (nodup_prefix_suffix (TBS ++ LBc) LM tk 72 72 (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) INtkB Hin). }
pose proof (heap_presx_refl A4H xlocA L0 sp0 m) as HPX.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(sp0 - 432, sp0); (tk, tk + 72)] m) as MU.
unfold tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote] in TOK.
stash PB. stash TSK. stash STR. stash MODE. stash KL. stash KR. stash G.
unfold A_PE_ENTRY, LOCCELL_A, LOCALE_LOCK_A, A_ERRNO, A_TP in *.
reenterA asegs A4L HIx asegs_wx HP.
step. carve_frame 432%nat ST.
stepz. do 13 step. step. step.
rewrite (unsigned_lit (sp0 + -416)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (sp0 + -416 - (sp0 + -416) mod 32) with (sp0 + -432) by (clear - SPA; Z.div_mod_to_equations; lia).
step. stepz. step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX1 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP MU WM SUBa ltac:(lia)); pe_px_solve1 tk INtk NTK]);
unstash G; assert (G1 : GA mc) by (eapply GA_outside; [exact G | exact MU | exact WM | pe_img_solve]); clear G
end.
clear HPX.
evt_done5.
eapply (hiA_stack_malloc A4L HIx) with (k := 2) (bytes := 224) (lo := lo) (LB := TBS ++ LBc) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | rewrite fr_size_2; lia | reflexivity | (clear - FRN; lia) | .. ].
all: rewrite ?unsigned_lit by lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
destruct (OBL_ERRNO _ _ _ _ _ _ _ HP1) as (errv1 & ERR1).
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (HPX2 : heap_presx A4H xlocA L0 sp0 m m1').
{ eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR1 | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply INCL0; exact Hb | apply in_or_app; right; exact Hb]. }
assert (G2 : GA m1') by (eapply GA_pres; [exact HPR1 | exact G1]).
clear HPX1 G1.

assert (INF : In (Fr, 2) ((Fr, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ tk 72 HP1 INtk) as APt.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF INtk) as DFt.
rewrite fr_size_2 in HFal, HFc, HFimg, HFapp, DFt. rewrite fr_shadow_len_2 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp, APt.
destruct (own_frame_freshG HIx Fr (TBS ++ LBc) LB0 LM FRS B A1 m1' md1 HP1 INCL0) as [OFF OFS]. fold L0 in OFF, OFS.
assert (SUBb : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUBa b Hb) as [H | H]; [left; exact H | right; cbn [fr_ivs flat_map app]; right; right; exact H]. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
assert (LOCcs : forall a, 6444320 - 48 <= a < 6444320 - 48 + 8 -> hl_client_static A4H a).
{ intros a Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LOC; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia].
clear SB1 SB2 SB3 UARC PEPC ERR.
pose proof (RTC_PEPC _ _ _ _ _ _ _ HP1) as PEPC. apply ro_C8_of_bytes_at in PEPC. unfold A_GOT_PEPC in PEPC.
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 32 (repeat (Z_to_bv 8 0) 32)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_2 in FF1. change (Z.to_nat (256 - 8)) with 248%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 32 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
clear MU WM. pose proof (wmono_refl asegs m1') as WM. pose proof (munch_refl [(sp0 - 432, sp0); (tk, tk + 72); (Fr, Fr + 248); (sh, sh + 32)] m1') as MU.
unfold A_SB in APt, HFapp.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. if_truex.
stepz. stepz.
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. stepz. stepz. stepz. step. step.
fold sh.
do 4 stepz. step. do 24 stepz. stepz. stepz. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mP end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX3 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX2 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP1 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (G3 : GA mc) by (eapply GA_outside; [exact G2 | exact MU | exact WM | pe_img_solve])
end.
clear HPX2 G2.

eapply evt_cut; [eapply USE; [exact LOC | unfold GLOBLOC_A; lia | lia | reflexivity | eassumption] |].
intros ms3 (m3 & a1x & a2x & a3x & a4x & -> & MU3 & WM3 & MI3 & LOC3).
replace (ret_pc (Z_to_bv 64 0x93b9c)) with (Z_to_bv 64 0x93b9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA GLOBLOC_A 0) with GLOBLOC_A in LOC3 by reflexivity.
replace (usl_retA GLOBLOC_A) with LC_GLOBAL_A by reflexivity.
assert (HP2 : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B mP md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP1 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP1 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | exact MI1]. }
assert (HPX4 : heap_presx A4H xlocA L0 sp0 m m3)
by (eapply heap_presx_trans; [exact HPX3 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP2 MU3 WM3 SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]).
assert (G4 : GA m3) by (exact (GA_loc _ _ G3 MU3 WM3)).
assert (HP3 : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B m3 md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP2 MU3); pe_fw_solve tk Fr sh INtk INF | exact WM3 | exact MI3]. }
clear HPX3 G3 HP2.
unfold LOCCELL_A, A_TP in MU3, LOC3.

eapply rw_cells_transport in TOK; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LCK; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR1; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply ro_cells_transport in PEPC; [| exact MU3 | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (ST3 : stk asegs m3 lo (sp0 + -432)).
{ eapply stk_transport; [exact ST1 | exact MU3 | exact WM3 |]. intros z Hz. left. cbn [outside]. lia. }
clear ST1 MU WM MU3 WM3 MI1 LOC.
pose proof (wmono_refl asegs m3) as WM. pose proof (munch_refl [(sp0 - 432, sp0); (tk, tk + 72)] m3) as MU.
assert (SHT3 : ro_cells asegs m3 (tk / 8 + 2147450880)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP3 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
set (sht := tk / 8 + 2147450880) in *.
assert (SHTR : 2147450880 <= sht /\ sht + 9 <= 17594333495296) by (unfold sht; clear - Htlo Hthi ACR; Z.div_mod_to_equations; lia).
stepz. stepz.
step.
step. if_truex.
step. step. ub_land Htal. step. ub_if_lit.
step. step. step. step.
rewrite (unsigned_lit (tk + 32)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (div8_add tk 32) by (clear - Htal; Z.div_mod_to_equations; lia). change (32 / 8) with 4.
replace (tk / 8 + 4 + 2147450880) with (sht + 4) by (unfold sht; lia).
stepz.
step. rewrite ?sxb_zero. step. if_true.
stepz.
step. step. step.
rewrite (unsigned_lit (tk + 36)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite (div8_add tk 36) by (clear - Htal; Z.div_mod_to_equations; lia). change (36 / 8) with 4.
replace (tk / 8 + 4 + 2147450880) with (sht + 4) by (unfold sht; lia).
stepz.
step. rewrite ?sxb_zero. step. if_true.
step. stepz.
step.
step.

unstash MODE.
assert (LRR : 0 <= lenr < 2^64 /\ (lenr = len \/ (lenr = LENW_C /\ 1 <= len))) by (destruct MODE as [_ [-> | (-> & L1 & _)]]; unfold LENW_C; lia).
assert (PLOC : len = 0 \/ (exists b, In b LBc /\ blk_addr b <= sb /\ sb + len <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= sb /\ sb + len <= Fh + fr_size kh - 8 /\ unpoisoned asegs m A_SB sb len)) by (exact (proj1 MODE)).
stash MODE.

assert (JOIN : forall (mJ : word -> option byte) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j0 j1 j2 j3 j4 j7 j8 jg j5 j6 : list byte),
rw_cells asegs mJ tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells asegs mJ (sp0 + -432) [CB 16 j0; C8 (Z_to_bv 64 0); CB 128 j1; C8 (Z_to_bv 64 LC_GLOBAL_A); C8 (Z_to_bv 64 (tk + 36)); CB 16 j2; C8 (Z_to_bv 64 (sht + 4));
C8 (Z_to_bv 64 Fr); C8 (Z_to_bv 64 Fr); C8 (Z_to_bv 64 (tk + 32)); CB 24 j3; C8 (Z_to_bv 64 tk); C8 (Z_to_bv 64 lenr); CB 24 j4;
C8 (Z_to_bv 64 (sht + 4)); CB 8 j7; C8 (Z_to_bv 64 Fr); CB 4 j8; C4 (Z_to_bv 64 0); CB 16 jg;
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mJ Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 75392); C8 (Z_to_bv 64 A_PE_ENTRY); CB 40 j5; C1 (Z_to_bv 8 1); CB 183 j6] ->
rw_cells asegs mJ sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242);
C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243);
C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)] ->
rw_cells asegs mJ 6576272 [C4 (Z_to_bv 64 0)] ->
rw_cells asegs mJ (6444320 - 164) [C4 errv1] ->
rw_cells asegs mJ (6444320 - 48) [C8 (Z_to_bv 64 GLOBLOC_A)] ->
stk asegs mJ lo (sp0 + -432) -> munch [(lo, sp0); (tk, tk + 72)] m3 mJ -> wmono asegs m3 mJ -> mem_inv asegs mJ ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (sp0 + -432)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 (Z_to_bv 64 sp0) (Z_to_bv 64 (sp0 + -432)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 sh) (Z_to_bv 64 tk) (Z_to_bv 64 sb) (Z_to_bv 64 tk) (Z_to_bv 64 Fr) s7 s8 s9
(Z_to_bv 64 2147450880) s11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x93cf8) fc None mJ (seg_rom asegs))).
{ clear TOK FR FF1 FSH1 LCK ERR1 LOC3 ST3 MU WM MI3 SHT3 PEPC.
intros mJ xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 j0 j1 j2 j3 j4 j7 j8 jg j5 j6 TOK FR FF1 FSH1 LCK ERR1 LOC3 ST3 MU WM MIJ.

assert (HPX5 : heap_presx A4H xlocA L0 sp0 m mJ)
by (eapply heap_presx_trans; [exact HPX4 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP3 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]).
assert (G5 : GA mJ) by (eapply GA_outside; [exact G4 | exact MU | exact WM | pe_img_solve]).
assert (HPJ : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B mJ md1).
{ eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP3 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | exact MIJ]. }
clear HPX4 G4 MU WM.
pose proof (wmono_refl asegs mJ) as WM. pose proof (munch_refl [(sp0 - 432, sp0)] mJ) as MU.

step. step.
evt_done5.
eapply (DUP) with (LB := TBS ++ LBc) (LM := LM) (FRS := (Fr, 2) :: FRS) (B := B) (lo := lo) (errv := errv1);
[ heap_nowA A4L HIx HPJ MU WM MIJ
| rewrite unsigned_lit by lia; exact ST3 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR1 | reflexivity
| rewrite unsigned_lit by lia; reflexivity | exact LMN | exact BM1 | ].
intros ms5 m5 md5 A5 rd errv5 RS5 VM5 ST5 HPR5 ERR5 OUT5. open_ret RS5.
rewrite (unsigned_lit (sp0 + -432)) in ST5, HPR5 by lia.

lazymatch type of HPR5 with heap_pres _ _ _ ?mc _ =>
assert (HPX6 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX5 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HPJ MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (G6 : GA mc) by (eapply GA_outside; [exact G5 | exact MU | exact WM | pe_img_solve])
end.
assert (SUBc : forall b, In b L0 -> In b ((TBS ++ LBc) ++ LM ++ fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. unfold L0 in Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply INCL0; exact Hb|]. apply in_or_app; right.
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (HPX7 : heap_presx A4H xlocA L0 sp0 m m5).
{ eapply heap_presx_trans; [exact HPX6|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR5 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (G7 : GA m5) by (eapply GA_pres; [exact HPR5 | exact G6]).
clear HPX5 G5 HPX6 G6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in LCK; [| right; left; cbn; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR5.
clear MU WM MIJ ST3 ERR1 HPJ.

assert (STCJ : forall nl mdl, PE_STATIC_A HIx (PEF tk 0 0 len lenr sb (sp0 + -432) mdl mxd fl) (PEFA sp0 Fr LC_GLOBAL_A nl bsl dsl) lo).
{ intros nl mdl. unfold PE_STATIC_A, pe_geomA, LENR_OK; cbn [pf_spf pf_len pf_lenr pf_sb pf_md pf_mxd pf_fl pf_tk pa_sp0 pa_F].
repeat split; try (clear - LO LOS SPA HT SP62 SP0R PLEN LEN SB0 SBL LRR MXB HFal HF0 HFc Htal ACR; first [lia | Z.div_mod_to_equations; lia]). }
assert (EXIT : forall (mX : word -> option byte) (mdX : config) (AX : ASA A4L HIx) (BX : bud) (errvX : word) (eX : Z) (jsl jgx jffx jshx : list byte)
(y1 u0' u1' u2' w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z8 z9 z10 z11 u3' u4' u5' u6' : word),
HEAPAx AX (TBS ++ LBc) LM ((Fr, 2) :: FRS) BX mX mdX ->
rw_cells asegs mX tk [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 pb); C4 (Z_to_bv 64 mxd); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 eX); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 q); C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0)] ->
rw_cells asegs mX (sp0 + -432) [CB 312 jsl] -> rw_cells asegs mX (sp0 + -120) [CB 16 jgx] ->
rw_cells asegs mX (sp0 - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mX Fr [CB 248 jffx] -> rw_cells asegs mX sh [CB 32 jshx] ->
stk asegs mX lo (sp0 + -432) -> rw_cells asegs mX (6444320 - 164) [C4 errvX] -> rw_cells asegs mX (6444320 - 48) [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA L0 sp0 m mX -> GA mX -> model_vm_only (cfg_model md) (cfg_model mdX) -> bB B <= bB BX -> bD B - M2D <= bD BX ->
AJ5 A4L HIx AX T mdX
(MS (mkR y1 (Z_to_bv 64 (sp0 + -432)) gp (Z_to_bv 64 6444320) u0' u1' u2' (Z_to_bv 64 sp0) (Z_to_bv 64 (sp0 + -432)) (Z_to_bv 64 0) w1 w2 w3 w4 w5 w6 w7
(Z_to_bv 64 sh) z3 z4 z5 (Z_to_bv 64 Fr) (Z_to_bv 64 Fr) z8 z9 z10 z11 u3' u4' u5' u6')
F (Z_to_bv 64 0x93c30) fc None mX (seg_rom asegs))).
{ clear TOK FR FF1 FSH1 LCK ERR5 LOC3 ST5.
intros mX mdX AX BX errvX eX jsl jgx jffx jshx y1 u0' u1' u2' w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z8 z9 z10 z11 u3' u4' u5' u6' HPXh TOKX SLX GAPX SVX FFX FSHX STX ERRX LOCX HPXX GX VMX BBX BDX.
assert (INq0 : In (q, 32 * mxd) L0) by (unfold L0, LB0; left; reflexivity).
assert (INpbs : incl pbs L0) by (intros b Hb; unfold L0, LB0; right; apply in_or_app; left; apply in_or_app; left; exact Hb).
assert (AGq : agree_on asegs ((q, 32 * mxd) :: pbs) m mX).
{ eapply (agree_of_heap_presx asegs A4H); [exact HPXX | reflexivity |]. intros b [<- | Hb]; [exact INq0 | exact (INpbs b Hb)]. }
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
unstash PB. unstash TSK. unstash KR.
unfold APE_EPI1.
eapply (out_finish_BG HIx GA GA_outside (PEF tk 0 0 len lenr sb (sp0 + -432) (cfg_model mdX) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A 0 bsl dsl) LBc [] LM FRS m lo mX mdX md AX BX [] TBS 0
sv errvX T jsl jgx jffx jshx) with (F0 := F) (fc0 := fc);
[ exact (STCJ 0 (cfg_model mdX)) | | | left; split; reflexivity | exact SLX | | exact SVX | exact FFX | exact FSHX | exact STX | exact ERRX | exact LOCX | | exact VMX | exact GX | | | | apply fsaved_refl | intros Hf; exact Hf | ].
- eapply (heapA_perm A4L HIx); [exact HPXh | cbn [app]; apply Permutation_refl | apply Permutation_refl | apply Permutation_refl].
- exists q, pb, 0, pbs, (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1)), (TS (wz 0) (wz 0) (wz 0) (Z_to_bv 64 eX) (wz 0) (wz 0) (Z_to_bv 8 0)).
split; [rewrite ECC, app_nil_r; exact ETBS|]. split; [cbn [length pf_mxd]; rewrite repeat_length; lia|]. split; [cbn [pf_mxd pf_fl]; lia|].
split; [unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd pf_fl pf_tk]; exact TOKX|].
split; [eapply (pbuf_agree asegs); [exact PB | exact AGq | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AGq |]. exists q, (32 * mxd). split; [left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl) as Hi. cbn [length] in Hi. rewrite repeat_length in Hi. cbn [pf_mxd]. lia. }
split.
+ intros i li Hli Hile. assert (i = 0%nat) as -> by lia. cbn in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. destruct i as [|i]; [lia|]. change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. apply lvl_zero_clean.
- cbn [pf_spf pa_sp0]. replace (Z.to_nat (sp0 - 104 - (sp0 + -432 + 312))) with 16%nat by lia. replace (sp0 + -432 + 312) with (sp0 + -120) by lia. exact GAPX.
- cbn [pa_sp0]. eapply heap_presx_weaken; [exact HPXX | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0, LB0. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- cbn [pa_bslack app]. unfold K_free, K_exit in *. lia.
- cbn [pa_dslack]. lia.
- exact RAE.
- intros ms' md' A' P. apply KR. eapply pe_post_A_eq; [| | | | | | | exact P]; reflexivity. }
destruct OUT5 as [(Erd & Eerr & HP5) | (Hrd & (jd & DBLK) & HP5)].
-
subst rd errv5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
assert (SHT5 : ro_cells asegs m5 sht
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP5 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
pose proof (OBL_SH_ERRNO _ _ _ _ _ _ _ HP5) as SHE. apply ro_C1_of_bytes_at in SHE. change (A_ERRNO / 8 + A_SB) with 2148256399 in SHE.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(sp0 - 432, sp0); (tk, tk + 72)] m5) as MU.
unfold ENOMEMv in ERR5. change (6444320 - 164) with 6444156 in ERR5.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. step. if_false.
step.
eapply evt_cut; [eapply ERRNOL; reflexivity |]. intros ms9 ->.
replace (ret_pc (Z_to_bv 64 0x93d10)) with (Z_to_bv 64 0x93d10) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
unfold A_ERRNO, A_TP.
step. ub_if_lit.
step. step. ub_if_lit.
step. step. step. rewrite ?sxb_zero. step. if_true.
step. norm_sx32. step. step. step. step. step. if_false.
step. step. rewrite ?sxb_zero. step. if_true.
step. step. step. step. stepz.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXe : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX7 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP5 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (Ge : GA mc) by (eapply GA_outside; [exact G7 | exact MU | exact WM | pe_img_solve]);
assert (HPe : HEAPAx A5 (TBS ++ LBc) LM ((Fr, 2) :: FRS) (charge B 0 M2D) mc md5) by (heap_nowA A4L HIx HP5 MU WM MI5)
end.
lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval cbv in (length cs - 14)%nat in rewrite <- (firstn_skipn n cs) in FR end. cbn [firstn skipn] in FR.
lazymatch type of FR with rw_cells _ ?mm ?a (?x ++ ?y) => change (rw_cells asegs mm a ([] ++ x ++ y)) in FR end.
apply rw_cells_merge in FR. cbn [app] in FR.
lazymatch type of FR with rw_cells _ _ _ (CB ?n ?b :: ?g :: ?post) => let v := eval vm_compute in n in change n with v in FR; change (CB v b :: g :: post) with ([CB v b] ++ [g] ++ post) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [SL FR]. cbn [cells_size csize Nat.add] in FR. change (Z.of_nat 312) with 312 in FR.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [GAP SV]. cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 16) with 16 in SV.
replace (sp0 + -432 + 312 + 16) with (sp0 - 104) in SV by lia. replace (sp0 + -432 + 312) with (sp0 + -120) in GAP by lia.
lazymatch type of FF1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FF1 end. apply rw_cells_merge in FF1. cbn [app] in FF1.
lazymatch type of FF1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FF1 end.
lazymatch type of FSH1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FSH1 end. apply rw_cells_merge in FSH1. cbn [app] in FSH1.
lazymatch type of FSH1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FSH1 end.
evt_done5.
eapply (EXIT _ md5 A5 (charge B 0 M2D) (Z_to_bv 64 12) 16); [exact HPe | exact TOK | exact SL | exact GAP | exact SV | exact FF1 | exact FSH1 | exact ST5 | exact ERR5 | exact LOC3 | exact HPXe | exact Ge
| eapply model_vm_only_trans; [exact VM1 | exact VM5] | cbn [bB charge]; lia | cbn [bD charge]; lia].
-
assert (INd : In (rd, 48) ((TBS ++ LBc) ++ (rd, 48) :: LM)) by (apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ rd 48 HP5 INd) as (_ & Hdal & Hdlo & Hdhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ rd 48 HP5 INd) as Himg_d. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_d.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. change (hl_segs A4L) with asegs in MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [(sp0 - 432, sp0)] m5) as MU.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. step. if_truex.
step. step. step. step. step.
evt_done5.
eapply (NEWL) with (LB := TBS ++ LBc) (LM := (rd, 48) :: LM) (FRS := (Fr, 2) :: FRS) (B := charge B 0 M2D) (lo := lo) (d := rd) (junk := jd) (errv := errv5);
[ exact HP5 | left; reflexivity | exact DBLK | exact LCK | rewrite unsigned_lit by lia; exact ST5 | exact LO | rewrite unsigned_lit by lia; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR5 | reflexivity
| rewrite unsigned_lit by lia; reflexivity | ].
intros ms6 m6 rn jn RS6 ST6 HPR6 DBLK6 LCK6 ERR6 HP6 Hrn. open_ret RS6.
rewrite (unsigned_lit (sp0 + -432)) in ST6, HPR6 by lia.
rewrite lb_remove_head in HPR6.
assert (HPX8 : heap_presx A4H xlocA L0 sp0 m m6).
{ eapply heap_presx_trans; [exact HPX7|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR6 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (G8 : GA m6) by (eapply GA_pres; [exact HPR6 | exact G7]).
clear HPX7 G7.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR6.
clear MU WM MI5 ST5 ERR5 DBLK LCK LCK6.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI6. change (hl_segs A4L) with asegs in MI6.
pose proof (wmono_refl asegs m6) as WM. pose proof (munch_refl [(sp0 - 432, sp0); (tk, tk + 72)] m6) as MU.
assert (SHT6 : ro_cells asegs m6 sht
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP6 INtkB) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. exact SH. }
assert (INtk6 : In (tk, 72) ((TBS ++ LBc) ++ (rd, 48) :: LM)) by (apply in_or_app; left; exact INtkB).
assert (SUBd : forall b, In b L0 -> In b ((TBS ++ LBc) ++ (rd, 48) :: LM) \/ In b (fr_ivs A4L ((Fr, 2) :: FRS))).
{ intros b Hb. destruct (SUBb b Hb) as [H | H]; [left | right; exact H]. apply in_app_or in H as [H | H]; apply in_or_app; [left; exact H | right; right; exact H]. }
reenterA asegs A4L HIx asegs_wx HP6.
destruct Hrn as [-> | ->].
2:{
step. if_false. step.
step. step. rewrite ?sxb_zero. step. if_true.
step. step. stepz. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXf : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX8 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]);
assert (Gf : GA mc) by (eapply GA_outside; [exact G8 | exact MU | exact WM | pe_img_solve])
end.
evt_done5.
eapply (FREEL) with (LB := TBS ++ LBc) (LM := (rd, 48) :: LM) (FRS := (Fr, 2) :: FRS) (B := charge B 0 M2D) (d := rd) (n := 48) (lo := lo) (errv := errv5);
[ heap_nowA A4L HIx HP6 MU WM MI6 | left; reflexivity | rewrite unsigned_lit by lia; exact ST6 | exact LO | rewrite unsigned_lit by lia; cbn [hl_stack A4H]; lia
| rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia | rewrite unsigned_lit by lia; lia | exact ERR6 | reflexivity | rewrite unsigned_lit by lia; reflexivity | ].
intros ms9 m9 md9 A9 r9 RS9 VM9 ST9 HPR9 ERR9 HP9. open_ret RS9.
rewrite (unsigned_lit (sp0 + -432)) in ST9, HPR9 by lia.
rewrite lb_remove_head in HPR9, HP9.
assert (HPXg : heap_presx A4H xlocA L0 sp0 m m9).
{ eapply heap_presx_trans; [exact HPXf|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPR9 | lia | exact SUBc | intros a Xa; exact Xa]. }
assert (Gg : GA m9) by (eapply GA_pres; [exact HPR9 | exact Gf]).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in TOK; [| eapply client_range_block; [apply in_or_app; left; exact INtkB | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in LOC3; [| right; left; cbn; intros z Hz; apply LOCcs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FF1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; left; rewrite fr_size_2; reflexivity | lia | cbn; lia]].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR9) in FSH1;
[| eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; cbn [fr_ivs flat_map app fr_base fr_class fst snd]; right; left; rewrite fr_shadow_len_2; reflexivity
| unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; lia | unfold sh, shad; cbn [hl_sb A4L]; unfold A_SB; cbn; lia]].
a4l. unfold A_ERRNO, A_TP in ERR9.
clear MU WM MI6.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP9) as MI9. change (hl_segs A4L) with asegs in MI9.
pose proof (wmono_refl asegs m9) as WM. pose proof (munch_refl [(sp0 - 432, sp0)] m9) as MU.
reenterA asegs A4L HIx asegs_wx HP9.
step. step.
lazymatch type of FR with rw_cells _ _ _ ?cs => let n := eval cbv in (length cs - 14)%nat in rewrite <- (firstn_skipn n cs) in FR end. cbn [firstn skipn] in FR.
lazymatch type of FR with rw_cells _ ?mm ?a (?x ++ ?y) => change (rw_cells asegs mm a ([] ++ x ++ y)) in FR end.
apply rw_cells_merge in FR. cbn [app] in FR.
lazymatch type of FR with rw_cells _ _ _ (CB ?n ?b :: ?g :: ?post) => let v := eval vm_compute in n in change n with v in FR; change (CB v b :: g :: post) with ([CB v b] ++ [g] ++ post) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [SL FR]. cbn [cells_size csize Nat.add] in FR. change (Z.of_nat 312) with 312 in FR.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR. destruct FR as [GAP SV]. cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 16) with 16 in SV.
replace (sp0 + -432 + 312 + 16) with (sp0 - 104) in SV by lia. replace (sp0 + -432 + 312) with (sp0 + -120) in GAP by lia.
lazymatch type of FF1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FF1 end. apply rw_cells_merge in FF1. cbn [app] in FF1.
lazymatch type of FF1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FF1 end.
lazymatch type of FSH1 with rw_cells _ ?mm ?a ?cs => change (rw_cells asegs mm a ([] ++ cs ++ [])) in FSH1 end. apply rw_cells_merge in FSH1. cbn [app] in FSH1.
lazymatch type of FSH1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FSH1 end.
evt_done5.
eapply (EXIT _ md9 A9 (charge B 0 M2D) errv5 16); [exact HP9 | exact TOK | exact SL | exact GAP | exact SV | exact FF1 | exact FSH1 | exact ST9 | exact ERR9 | exact LOC3 | exact HPXg | exact Gg
| eapply model_vm_only_trans; [exact VM1 | eapply model_vm_only_trans; [exact VM5 | exact VM9]] | cbn [bB charge]; lia | cbn [bD charge]; lia]. }
step. if_truex.
step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz.
stepz. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPX9 : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX8 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]);
assert (G9 : GA mc) by (eapply GA_outside; [exact G8 | exact MU | exact WM | pe_img_solve]);
assert (HP6' : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mc md5) by (heap_nowA A4L HIx HP6 MU WM MI6)
end.
eapply evt_cut; [eapply USE; [exact LOC3 | unfold GLOBLOC_A; lia | split; [lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi; lia] | reflexivity | eassumption] |].
intros ms7 (mu7 & a1y & a2y & a3y & a4y & -> & MU7 & WM7 & MI7 & LOC7).
replace (ret_pc (Z_to_bv 64 0x93e84)) with (Z_to_bv 64 0x93e84) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
replace (usl_newA GLOBLOC_A rd) with rd in LOC7
by (unfold usl_newA; destruct (Z.eqb_spec rd 0); [lia|]; destruct (Z.eqb_spec rd LC_GLOBAL_A); [unfold LC_GLOBAL_A in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi; lia | reflexivity]).
assert (HPX10 : heap_presx A4H xlocA L0 sp0 m mu7)
by (eapply heap_presx_trans; [exact HPX9 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP6' MU7 WM7 SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]).
assert (G10 : GA mu7) by (exact (GA_loc _ _ G9 MU7 WM7)).
assert (HP7 : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mu7 md5).
{ eapply (heapA_client_frame A4L HIx); [exact HP6' | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP6' MU7); pe_fw_solve tk Fr sh INtk6 INF | exact WM7 | exact MI7]. }
clear HPX8 G8 HPX9 G9 HP6'.
unfold LOCCELL_A, A_TP in MU7, LOC7.
eapply rw_cells_transport in TOK; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR6; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in DBLK6; [| exact MU7 | exact WM7 | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (ST7 : stk asegs mu7 lo (sp0 + -432)).
{ eapply stk_transport; [exact ST6 | exact MU7 | exact WM7 |]. intros z Hz. left. cbn [outside]. lia. }
clear ST6 MU WM MU7 WM7 MI6 LOC3.
pose proof (wmono_refl asegs mu7) as WM. pose proof (munch_refl [(sp0 - 432, sp0)] mu7) as MU.
stepz.
step. step. step. step. stepz.
step. stepz. step. stepz. step. stepz. step. stepz. step. stepz. step. stepz.
step. step. step. stepz.
step. stepz. step. stepz. step. step. stepz. step.
step. stepz. step. stepz. step. stepz. step. step. stepz.
step. stepz. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mL end.
assert (HPX11 : heap_presx A4H xlocA L0 sp0 m mL)
by (eapply heap_presx_trans; [exact HPX10 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP7 MU WM SUBd ltac:(lia)); pe_px_solve1 tk INtk6 NTK]).
assert (G11 : GA mL) by (eapply GA_outside; [exact G10 | exact MU | exact WM | pe_img_solve]).
assert (HP8 : HEAPAx A5 (TBS ++ LBc) ((rd, 48) :: LM) ((Fr, 2) :: FRS) (charge B 0 M2D) mL md5) by (heap_nowA A4L HIx HP7 MU WM MI7).
clear HPX10 G10.

rewrite ?(unsigned_lit (tk + 20)), ?(unsigned_lit (tk + 32)), ?(unsigned_lit (tk + 56)), ?(unsigned_lit (tk + 64)) by lia.
rewrite ?(unsigned_lit (tk + 20)), ?(unsigned_lit (tk + 32)), ?(unsigned_lit (tk + 56)), ?(unsigned_lit (tk + 64)) in FR by lia.
rewrite ?Z.shiftr_div_pow2 by lia. rewrite ?Z.shiftr_div_pow2 in FR by lia. change (2^3) with 8 in *.
rewrite ?(div8_add tk 20), ?(div8_add tk 56), ?(div8_add tk 64) by (clear - Htal; Z.div_mod_to_equations; lia).
rewrite ?(div8_add tk 20), ?(div8_add tk 56), ?(div8_add tk 64) in FR by (clear - Htal; Z.div_mod_to_equations; lia).
change (20 / 8) with 2 in *. change (56 / 8) with 7 in *. change (64 / 8) with 8 in *.
rewrite ?land7_mod8 by lia. rewrite ?land7_mod8 in FR by lia.
replace (tk / 8 + 2 + 2147450880) with (tk / 8 + SB2) by (unfold SB2; lia).
replace (Z_to_bv 64 sb) with (Z_to_bv 64 (sb + 0)) by (f_equal; lia).
replace (sht + 4) with (tk / 8 + 4 + A_SB) in FR by (unfold sht, A_SB; lia).
replace (tk / 8 + 2 + 2147450880) with (tk / 8 + 2 + A_SB) in FR by (unfold A_SB; lia).
replace (tk / 8 + 7 + 2147450880) with (tk / 8 + 7 + A_SB) in FR by (unfold A_SB; lia).
replace (tk / 8 + 8 + 2147450880) with (tk / 8 + 8 + A_SB) in FR by (unfold A_SB; lia).
evt_done5. unstash KL.
lazymatch type of FR with rw_cells _ _ _ (CB 8 ?J0 :: _) => lazymatch type of FR with context [C4 _ :: CB 16 ?JG :: _] =>
lazymatch type of FF1 with rw_cells _ _ _ [C8 ?h0; C8 ?h1; C8 ?h2; CB 40 ?J5; _; CB 183 ?J6] =>
eapply (KL rd (sp0 + -432) Fr mL md5 A5 (charge B 0 M2D) (Z_to_bv 64 0)
(PEJA [] (le_bytes_to_word J0) (Z_to_bv 64 0) (Z_to_bv 64 0) j7 j8 JG (le8 h0 ++ le8 h1 ++ le8 h2) J5 J6) errv5)
end end end.
+
unfold PE_STATIC_A, pe_geomA, LENR_OK; cbn [pf_spf pf_len pf_lenr pf_sb pf_md pf_mxd pf_fl pf_tk pa_sp0 pa_F].
repeat split; try (clear - LO LOS SPA HT SP62 SP0R PLEN LEN SB0 SBL LRR MXB HFal HF0 HFc Htal ACR; first [lia | Z.div_mod_to_equations; lia]).
+
assert (INq0 : In (q, 32 * mxd) L0) by (unfold L0, LB0; left; reflexivity).
assert (INpbs : incl pbs L0) by (intros b Hb; unfold L0, LB0; right; apply in_or_app; left; apply in_or_app; left; exact Hb).
assert (AGq : agree_on asegs ((q, 32 * mxd) :: pbs) m mL).
{ eapply (agree_of_heap_presx asegs A4H); [exact HPX11 | reflexivity |]. intros b [<- | Hb]; [exact INq0 | exact (INpbs b Hb)]. }
unstash PB. unstash TSK. unstash STR.
split.
* unfold PE_CORE_A, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj ts_choff pf_len pf_tk pf_spf pf_md pf_mxd pf_fl].
split; [cbn [length]; rewrite repeat_length; lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote Z.of_nat]; exact TOK|].
split; [eapply (pbuf_agree asegs); [exact PB | exact AGq | intros bb Hb; right; exact Hb]|].
split; [exact Hpb|].
split. { intros i l Hl. eapply (rw_cells_agree asegs); [exact (TSK i l Hl) | exact AGq |]. exists q, (32 * mxd). split; [left; reflexivity|].
rewrite srec_cells_size. pose proof (nth_error_Some_length Hl) as Hi. cbn [length] in Hi. rewrite repeat_length in Hi. lia. }

unfold pe_frameA; cbn [pf_spf pf_tk pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc].
lazymatch type of FR with rw_cells _ _ _ ?cs => rewrite <- (firstn_skipn 40 cs) in FR end. cbn [firstn skipn] in FR.
apply (proj1 (rw_cells_app asegs mL _ _ _)) in FR. destruct FR as [SL FR].
lazymatch type of FR with rw_cells _ _ (_ + Z.of_nat ?n) _ => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in FR end.
lazymatch type of FR with rw_cells _ ?mm ?a (?g :: ?post) => change (rw_cells asegs mm a ([g] ++ post)) in FR end.
apply (proj1 (rw_cells_app asegs mL _ _ _)) in FR. destruct FR as [GAP SV]. cbn [cells_size csize Nat.add] in SV. change (Z.of_nat 16) with 16 in SV.
replace (sp0 + -432 + 312 + 16) with (sp0 - 104) in SV by lia.
pose proof SL as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS.
pose proof FF1 as [[WFF _] _]. cbn [cells_wf cell_wf] in WFF.
lazymatch type of SL with rw_cells _ _ _ (CB 8 ?J :: _) => set (J0 := J) in * end.
assert (LJ0 : length J0 = 8%nat) by (clear - WFS; tauto).
assert (Lj7 : length j7 = 8%nat) by (clear - WFS; tauto).
assert (Lj8 : length j8 = 4%nat) by (clear - WFS; tauto).
split.
{ eapply rw_cells_recast; [exact SL | | | ].
- unfold pe_slotsA; cbn [cells_wf cell_wf pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pf_tk pf_lenr pa_F pa_newloc pa_oldloc]. clear - Lj7 Lj8. tauto.
- unfold pe_slotsA; cbn [cells_bytes cbytes app pj_0 pj_8 pj_16 pj_obj pj_288 pj_304 pf_tk pf_lenr pa_F pa_newloc pa_oldloc].
rewrite !Q8l1.Mq2.le8_of_bytes by (exact LJ0). reflexivity.
- reflexivity. }
split.
{
cbn [pj_gap]. replace (Z.to_nat (sp0 - 104 - (sp0 + -432 + 312))) with 16%nat by lia. exact GAP. }
split; [exact SV|].
split.
{ eapply rw_cells_recast; [exact FF1 | | | ].
- unfold ff_cellsA; cbn [cells_wf cell_wf pj_fhd pj_f1 pj_f2]. rewrite !length_app, !length_le8. clear - WFF. tauto.
- unfold ff_cellsA; cbn [cells_bytes cbytes app pj_fhd pj_f1 pj_f2]. rewrite <- !app_assoc. reflexivity.
- reflexivity. }
{ eapply rw_cells_recast; [exact FSH1 | | | ].
- unfold ffsh_cells, FSH0. cbn [map cells_wf cell_wf]. repeat split.
- unfold ffsh_cells, FSH0. cbn [map cells_bytes cbytes app repeat]. reflexivity.
- reflexivity. }
*
unfold PE_REST_A, ts_init; cbn [t_levels t_depth t_co t_x t_pb t_pbs t_obj t_objs t_objbs ts_choff pf_len pf_tk pf_spf pf_sb pf_md pf_mxd pf_fl pa_sp0 pa_F pa_bslack pa_dslack].
assert (ECC : concat (map lvl_blocks (lvl_reset :: repeat lvl_zero (Z.to_nat mxd - 1))) = @nil blk)
by (cbn [map concat lvl_blocks lvl_reset tl_cbs tl_nbs app]; rewrite concat_lvl_blocks_zero; reflexivity).
split.
{ eapply (heapA_perm A4L HIx); [exact HP8 | | apply Permutation_refl | apply Permutation_refl].
unfold pe_blocksA, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_tk pf_mxd]. rewrite ECC, ETBS. perm. }
split.
{ intros i li Hli. unfold lvl_cur.
destruct i as [|i].
- cbn in Hli. injection Hli as <-. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_reset Nat.ltb Nat.eqb Nat.leb].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|]. exists CNone, false. split; [reflexivity|]. split; [exact I|]. cbn. split; reflexivity.
- change (nth_error (repeat lvl_zero (Z.to_nat mxd - 1)) i = Some li) in Hli.
apply nth_error_repeat_some in Hli. subst li. cbn [tl_st tl_ss tl_cs tl_cbs tl_cur lvl_zero].
split; [lia|]. split; [lia|]. split; [cbn; split; reflexivity|].
replace (S i <? 0)%nat with false by reflexivity. replace (S i =? 0)%nat with false by reflexivity. apply lvl_zero_clean. }
split; [reflexivity|].
split; [exact ST7|]. split; [exact ERR6|].
split.
{ destruct PLOC as [Z0 | PL].
- destruct payload; [| cbn in PLEN; lia]. apply bytes_at_nil. lia.
- eapply (heap_presx_bytes_at A4H); [exact HPX11 | exact STR |]. rewrite PLEN.
destruct PL as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)].
+ destruct bb as [ba bn]. eapply client_rangex_block; [unfold L0, LB0; apply in_or_app; left; right; apply in_or_app; right; exact Hbb | exact Hb1 | exact Hb2].
+ eapply client_rangex_block; [unfold L0; apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFh | exact HF1 | lia]. }
split; [exact PLEN|].
split.
{ assert (PL0 : len = 0 \/ payload_locA (PEF tk 0 0 len lenr sb (sp0 + -432) (cfg_model md5) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A rd bsl dsl) LBc FRS m).
{ destruct PLOC as [Z0 | PL]; [left; exact Z0 | right]. unfold payload_locA; cbn [pf_sb pf_len]. exact PL. }
exact (payload_locA_presx HIx xlocA (PEF tk 0 0 len lenr sb (sp0 + -432) (cfg_model md5) mxd fl) (PEFA sp0 Fr LC_GLOBAL_A rd bsl dsl) LBc FRS _ _ _ _ _ _ _ LB0 sp0 m mL HP (incl_refl _) HPX11 PL0). }
split; [apply heap_presx_refl|]. split; [apply model_vm_only_refl|].
split; [exact G11|].
unfold PE_BUD, tstate_blocks; cbn [t_pbs t_objbs t_levels pa_bslack pa_dslack bB bD charge]. rewrite ECC, !app_nil_r.
rewrite ETBS in BB. cbn [app length] in BB. unfold K_free, K_exit in *. rewrite ?Nat2Z.inj_succ in BB. lia.
+ eapply model_vm_only_trans; [exact VM1 | exact VM5].
+ eapply heap_presx_weaken; [exact HPX11 | lia | | intros a Xa; exact Xa].
intros b Hb. unfold L0, LB0. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; right; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
+ eapply (agree_of_heap_presx asegs A4H); [exact HPX11 | reflexivity |]. intros b Hb. unfold L0, LB0. apply in_or_app; left. right. apply in_or_app; left. exact Hb.
+ exact LOC7.
+ unfold alloc_ceiling, sp_window_lo, stack_max_size in Hdhi. lia.
+ cbn [bB charge]. lia.
+ cbn [bD charge]. lia.
}

unstash MODE. destruct MODE as [_ [Elr | (Elr & LEN1 & (str0 & Ep & NONUL) & SLK & PAD & SLOC)]].
-
subst lenr. if_truex. stepz. stepz. step. if_truex.
eapply JOIN; [exact TOK | exact FR | exact FF1 | exact FSH1 | exact LCK | exact ERR1 | exact LOC3 | exact ST3
| eapply munch_weaken; [| exact MU]; intros z Hz; cbn [outside] in Hz |- *; lia | exact WM | eassumption].
-
subst lenr. replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) in * by (apply bv_eq; reflexivity).
if_lit true. stepz. stepz. step. if_lit false. step. step.
assert (ELEN : Z.of_nat (length str0) + 1 = len) by (subst payload; rewrite length_app in PLEN; cbn [length] in PLEN; lia).
assert (HI47 : sb + len + Z.of_nat (length slack) <= alloc_ceiling).
{ destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)].
- destruct bb as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; right; exact Hbb)) as (_ & _ & _ & Hhi & _). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFh) as (_ & _ & _ & Hhi & _). lia. }
unstash STR.
assert (CAT : bytes_at asegs m sb (str0 ++ Z_to_bv 8 0 :: slack)).
{ assert (C0 : bytes_at asegs m sb (payload ++ slack)) by (apply bytes_at_app; split; [exact STR | rewrite PLEN; exact SLK]).
subst payload. rewrite <- app_assoc in C0. cbn [app] in C0. exact C0. }
assert (LCAT : Z.of_nat (length (str0 ++ Z_to_bv 8 0 :: slack)) = len + Z.of_nat (length slack)) by (rewrite length_app; cbn [length]; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HPXc : heap_presx A4H xlocA L0 sp0 m mc)
by (eapply heap_presx_trans; [exact HPX4 | eapply (presx_private _ _ _ _ _ _ _ _ _ L0 sp0 HP3 MU WM SUBb ltac:(lia)); pe_px_solve tk Fr sh INtk NTK INF OFF OFS]);
assert (HPc : HEAPAx A1 (TBS ++ LBc) LM ((Fr, 2) :: FRS) B mc md1)
by (eapply (heapA_client_frame A4L HIx); [exact HP3 | eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP3 MU); pe_fw_solve tk Fr sh INtk INF | exact WM | eassumption]);
assert (CATc : bytes_at asegs mc sb (str0 ++ Z_to_bv 8 0 :: slack));
[ eapply (heap_presx_bytes_at A4H); [exact HPXc | exact CAT |]; rewrite LCAT;
destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)];
[ destruct bb as [ba bn]; eapply client_rangex_block; [unfold L0, LB0; apply in_or_app; left; right; apply in_or_app; right; exact Hbb | cbn [blk_addr blk_size fst snd] in *; lia | cbn [blk_addr blk_size fst snd] in *; lia]
| eapply client_rangex_block; [unfold L0; apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFh | exact HF1 | lia] ] |];
assert (UPc : unpoisoned asegs mc A_SB sb len);
[ destruct PLOC as [Z0 | [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)]]; [lia | |];
[ destruct bb as [ba bn]; cbn [blk_addr blk_size fst snd] in Hb1, Hb2;
eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ ba bn sb len HPc); [apply in_or_app; right; exact Hbb | exact Hb1 | exact Hb2 | lia]
| exact (unpoisoned_presx_frame HIx xlocA _ _ _ _ _ _ _ LB0 sp0 m mc Fh kh sb len HP HFh HF1 HF2 UPS HPXc) ] |];
assert (RTc : asan_rt_ok mc) by (exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc))
end.
assert (AM : 64 < len -> app_mem sb len).
{ intros _. unfold app_mem, A_HMB. destruct SLOC as [(bb & Hbb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2)].
- destruct bb as [ba bn]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ba bn HP ltac:(apply in_or_app; left; apply in_or_app; right; exact Hbb)) as AP. cbn [hl_sb A4L] in AP. unfold A_SB in *.
split; [lia|]. destruct AP as [AP | AP]; [left; lia | right; lia].
- pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFh) as AP. cbn [hl_sb A4L] in AP. unfold A_SB in *.
split; [lia|]. destruct AP as [AP | AP]; [left; lia | right; lia]. }
eapply (ISTRLEN) with (a := sb) (lo := lo) (s := str0) (slack := slack);
[ rewrite ELEN; exact UPc | exact RTc | exact SB0 | unfold alloc_ceiling, sp_window_lo, stack_max_size in HI47; lia | lia | rewrite ELEN; exact AM
| left; lia | reflexivity | exact NONUL | exact CATc | replace (sb + Z.of_nat (length str0) + 1) with (sb + len) by lia; exact PAD
| rewrite unsigned_lit by lia; eassumption | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; clear - SPA; Z.div_mod_to_equations; lia
| eassumption | rewrite unsigned_lit by lia; reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mS MUS WMS MIS STS.
rewrite (unsigned_lit (sp0 + -432)) in MUS, STS by lia.
replace (ret_pc (Z_to_bv 64 0x93cec)) with (Z_to_bv 64 0x93cec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
eapply rw_cells_transport in TOK; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FR; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FF1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in FSH1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LCK; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in ERR1; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
eapply rw_cells_transport in LOC3; [| exact MUS | exact WMS | cbn [disjoint_from cells_size csize Nat.add]; lia].
assert (MUJ : munch [(lo, sp0); (tk, tk + 72)] m3 mS).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUS]]; intros z Hz; cbn [outside] in Hz |- *; clear - Hz LO LOS; lia. }
pose proof (wmono_trans _ _ _ _ WM WMS) as WMJ.
clear MU WM. pose proof (wmono_refl asegs mS) as WM. pose proof (munch_refl [] mS) as MU.
step. step.
rewrite (unsigned_lit (Z.of_nat (length str0))) by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
step. if_false.
eapply JOIN; [exact TOK | exact FR | exact FF1 | exact FSH1 | exact LCK | exact ERR1 | exact LOC3 | exact STS | exact MUJ | exact WMJ | exact MIS].
Qed.
End PeSEntryB.
End RC__1.
