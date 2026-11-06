(* fs WRITER walk, image A (fs.asan): put's GROW arm, the composition of its first half - put's entry and both tests
   (lib/A/FSW_put_grow_entry.v fsw_pg_entry_run, a Theorem Labs lane) and the doubling loop (lib/A/FSW_put_grow.v fsw_pg_loop) -
   into one run from A_put to the call of the program function fuzz_realloc 0x829e8, with the loop's final candidate
   identified as the model's WriterSpec.newcap cap need. The second half (the call, the resume at 0x84268 and the two
   tails) continues from exactly this lemma's continuation.
   Model facts used by path: lib/Prog/WriterSpec.v dbl / newcap (:29-35); the fuel-stability step below is re-proved
   here because the walk's loop starts at 2 * cap (cap <> 0) or 4096 (cap = 0) with fuel 16 while newcap starts at
   cap with fuel 64. TEMPLATE (never a copied term): the bespoke ASan line's put_grow_to_call
   (a Theorem Labs lane's put_blocks.v:379-449) makes the same
   identification at :447-449 (`dbl 64 c need` with newcap c need, cap <> 0 and cap = 0) over its own engine. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_ret
FSW_writer_tbl FSW_put FSW_put_grow FSW_put_grow_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- the model side: the loop's candidate is newcap ---- *)
Lemma fsw_pgr_dbl_S : forall f c need,
  WriterSpec.dbl (S f) c need = if need <=? c then c else WriterSpec.dbl f (2 * c) need.
Proof. reflexivity. Qed.

(* more fuel than enough changes nothing *)
Lemma fsw_pgr_dbl_fuel : forall f g c need, 0 < c -> need <= c * 2 ^ Z.of_nat f -> (f <= g)%nat ->
  WriterSpec.dbl g c need = WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros g c need Hc Hn Hfg.
- cbn [Z.of_nat] in Hn. rewrite Z.pow_0_r, Z.mul_1_r in Hn.
  destruct g as [|g]; [reflexivity|]. rewrite fsw_pgr_dbl_S, (proj2 (Z.leb_le need c) Hn). reflexivity.
- destruct g as [|g]; [lia|]. rewrite !fsw_pgr_dbl_S.
  destruct (Z.leb_spec need c) as [H|H]; [reflexivity|]. cbv iota.
  apply IH; [lia | | lia].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia.
  replace (2 * c * 2 ^ Z.of_nat f) with (c * (2 * 2 ^ Z.of_nat f)) by ring. exact Hn.
Qed.

(* the walk's first candidate after fuel 16 is the model's newcap *)
Lemma fsw_pgr_newcap : forall cap need,
  (cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j) -> cap < need -> need <= WMAX ->
  WriterSpec.dbl 16 (if cap =? 0 then 4096 else 2 * cap) need = WriterSpec.newcap cap need.
Proof.
intros cap need Hc Hlt Hn. unfold WriterSpec.newcap, WMAX in *.
change (2 ^ 27) with 134217728 in Hn.
destruct Hc as [-> | (j & Hj & ->)].
- change (0 =? 0) with true. cbv iota.
  symmetry. apply fsw_pgr_dbl_fuel; [lia | | lia]. change (2 ^ Z.of_nat 16) with 65536. lia.
- assert (P : 1 <= 2 ^ j)
    by (pose proof (Z.pow_le_mono_r 2 0 j ltac:(lia) ltac:(lia)) as P0; change (2 ^ 0) with 1 in P0; exact P0).
  destruct (Z.eqb_spec (4096 * 2 ^ j) 0) as [E0|_]; [lia|]. cbv iota.
  rewrite (fsw_pgr_dbl_S 63), (proj2 (Z.leb_gt need _) Hlt). cbv iota.
  symmetry. apply fsw_pgr_dbl_fuel; [lia | | lia]. change (2 ^ Z.of_nat 16) with 65536. lia.
Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.

(* ---- put's grow arm, entry to the fuzz_realloc call (pc 0x829e8, ra = 0x84268). Premises: put_spec's own
   (lib/A/FSH_Fn_writer.v put_spec), narrowed to failed = 0 and the grow test; 0 <= n is put_spec's
   Z.of_nat (length bs) = n. The continuation gets the call-site state fsw_pg_ssc over an env that agrees with the
   entry env below atom 36, atom 36 = newcap cap need (a1, the size fuzz_realloc is asked for), the journal and ARU
   at the call, and the two memory facts: only put's frame was written, and presence was kept. ---- *)
Lemma fsw_pg_to_call :
  forall ly S U W regs mem md ch ot o n buf cap (text : list Z) Q,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap 0 text ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  0 <= n ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap < Z.of_nat (length text) + n + 1 ->
  (forall (E : env) (ms : machine_state) (mdc : Model),
     st_ok tfibsegs E fsw_pg_ssc (restrict (w_H W) ms) ->
     sh_ok tfibsegs fs_Bx fsw_pf_SH E (mrestrict (w_H W) (ms_mem ms)) ->
     ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
       ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms)) mdc 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) mdc ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FRAME_put <= a < spZ regs) ->
        ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
     YP06.env_agree 36
       (Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])) E ->
     ew E 36%nat = Z_to_bv 64 (WriterSpec.newcap cap (Z.of_nat (length text) + n + 1)) ->
     SRr tfibsegs W (mkCfg ms mdc) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md) Q.
Proof.
intros ly S U W regs mem md ch ot o n buf cap text Q HPRE G10 G12 HOUT Hspo Hoot Hot16 Hottop HPRESENT Hn0 HWM Hgrow
  K.
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
assert (Hcls : cap = 0 \/ exists j, 0 <= j <= 51 /\ cap = 4096 * 2 ^ j)
  by (destruct Hcase as [(Hc0 & _) | (Hj & _)]; [left; exact Hc0 | right; exact Hj]).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (_ & Hspc & Hsp47 & _).
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (fsw_pg_entry_run B HSS ly S U W regs mem md ch ot o n buf cap text Q HPRE G10 G12 HOUT Hspo Hoot Hot16
         Hottop HPRESENT Hn0 HWM Hgrow).
intros E ms mdc c HS SHOK HJ HARU HMEM HPR HAG E36 Hc.
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
unfold WMAX in HWM. change (2 ^ 27) with 134217728 in HWM.
(* the entry env's atoms the loop reads *)
set (Ee := Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap])) in *.
assert (A2 : ew E 2%nat = getr regs 2%bv)
  by (rewrite (proj1 HAG 2%nat ltac:(lia)); unfold Ee; apply ew_Ereg_nat; reflexivity).
assert (A12 : ew E 12%nat = Z_to_bv 64 n)
  by (rewrite (proj1 HAG 12%nat ltac:(lia)); unfold Ee; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact G12).
assert (A34 : ew E 34%nat = Z_to_bv 64 len)
  by (rewrite (proj1 HAG 34%nat ltac:(lia)); unfold Ee; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra;
      reflexivity).
assert (E2sp : bv_unsigned (ew E 2%nat) = spZ regs) by (rewrite A2; reflexivity).
(* the first candidate: its class and its bound *)
assert (HC : 4096 <= c /\ c <= 134217728 /\ (exists j, 0 <= j /\ c = 4096 * 2 ^ j)).
{ subst c. destruct Hcls as [-> | (j & Hj & ->)].
  - change (0 =? 0) with true. cbv iota. split; [lia|]. split; [lia|]. exists 0. split; [lia | reflexivity].
  - assert (P : 1 <= 2 ^ j)
      by (pose proof (Z.pow_le_mono_r 2 0 j ltac:(lia) ltac:(lia)) as P0; change (2 ^ 0) with 1 in P0; exact P0).
    destruct (Z.eqb_spec (4096 * 2 ^ j) 0) as [E0|_]; [lia|]. cbv iota.
    assert (Hj14 : j <= 14).
    { destruct (Z_le_gt_dec j 14) as [Hle|Hgt]; [exact Hle|]. exfalso.
      assert (P15 : 2 ^ 15 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
      change (2 ^ 15) with 32768 in P15. lia. }
    assert (P14 : 2 ^ j <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in P14.
    split; [lia|]. split; [lia|]. exists (j + 1). split; [lia|].
    rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. ring. }
destruct HC as (Hc1 & HcW & Hccls).
(* the need, as the loop's test reads it: n + 1 + len *)
assert (HU : YP0e.U E fsw_pg_need = len + n + 1).
{ unfold fsw_pg_need. rewrite U_SAlu, (U_atom E 34%nat len A34) by lia.
  rewrite U_SOff, A12, (wz n ltac:(lia)). cbn [zalu_raw].
  rewrite (zcanon_id (n + 1)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
apply (fsw_pg_loop B 16 W Q (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem)
         md [] ly S U 0 E ms mdc c (len + n + 1) (spZ regs) HS SHOK HJ HARU).
- (* the loop's write window: put's frame only, inside the journal's window *)
  intros E2 HA2.
  assert (E2sp2 : bv_unsigned (ew E2 2%nat) = spZ regs) by (rewrite (proj1 HA2 2%nat ltac:(lia)); exact E2sp).
  cbv [fsw_pg_ssl fsw_pg_mem ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
    [reflexivity | rewrite E2sp2; lia | cbv [YP09.r_wlo]; unfold FRAME_put; lia | cbv [YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fsw_pf_o_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- exact E2sp.
- exact E36.
- exact HU.
- exact Hc1.
- unfold WMAX. change (2 ^ 27) with 134217728. exact HcW.
- exact Hccls.
- unfold WMAX. change (2 ^ 27) with 134217728. lia.
- change (2 ^ Z.of_nat 16) with 65536. lia.
- intros E' ms' mdc' HA' Hew HS' SHOK' HJ' HARU' M1 PR1.
  apply (K E' ms' mdc' HS' SHOK' HJ' HARU').
  + intros a Ha Hna. rewrite (M1 a Ha Hna). exact (HMEM a Ha Hna).
  + intros a Ha. exact (PR1 a (HPR a Ha)).
  + eapply env_agree_trans; [exact HAG | exact HA'].
  + rewrite Hew. f_equal. subst c. apply fsw_pgr_newcap; [exact Hcls | exact Hgrow |].
    unfold WMAX. change (2 ^ 27) with 134217728. exact HWM.
Qed.

End w.
