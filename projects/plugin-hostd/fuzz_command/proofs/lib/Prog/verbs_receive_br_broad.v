From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import verbs_receive_br verbs_receive_br2 sup_broadcast_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma broad_text_len : forall R fn As ch, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_stub R fn As REC_MOD_HOST_SHAPE ch)) <= 28)%nat.
Proof.
  intros R fn As ch HC. unfold rec_stub. rewrite rec_answer_text.
  assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  destruct (r_refuse (rec_record R fn As) =? 0).
  - apply Nat.leb_le. vm_compute. reflexivity.
  - rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

Lemma broad_shl_cons : forall w ws, sup_host_setting_len (w :: ws) = Z.of_nat (length w) + 1 + sup_host_setting_len ws.
Proof. reflexivity. Qed.

Lemma broad_shl_nonneg : forall ws, 0 <= sup_host_setting_len ws.
Proof. induction ws as [|w ws IH]; [cbv; discriminate|]. rewrite broad_shl_cons. lia. Qed.

Lemma broad_shl_words : forall l cur,
  sup_host_setting_len (words_acc cur l) <= Z.of_nat (length cur) + Z.of_nat (length l) + 1.
Proof.
  induction l as [|b l IH]; intros cur; cbn [words_acc].
  - destruct cur as [|x cur]; [cbv; discriminate|]. rewrite broad_shl_cons.
    change (sup_host_setting_len []) with 0. cbn [length]. lia.
  - destruct (Verbs.is_sep b); cbv iota.
    + destruct cur as [|x cur]; cbv iota.
      * pose proof (IH []) as H. cbn [length] in *. lia.
      * rewrite broad_shl_cons. pose proof (IH []) as H. cbn [length] in *. lia.
    + pose proof (IH (cur ++ [b])) as H. rewrite length_app in H. cbn [length] in *. lia.
Qed.

Lemma broad_shl_firstn : forall n ws, sup_host_setting_len (firstn n ws) <= sup_host_setting_len ws.
Proof.
  induction n as [|n IH]; intros [|w ws]; cbn [firstn].
  - lia.
  - change (sup_host_setting_len []) with 0. exact (broad_shl_nonneg (w :: ws)).
  - lia.
  - rewrite !broad_shl_cons. pose proof (IH ws). lia.
Qed.

Lemma broad_shl_toks : forall D, sup_host_setting_len (toks D) <= Z.of_nat (length (line D)) + 1.
Proof.
  intros D. unfold toks, Verbs.words. pose proof (broad_shl_firstn line_words_max (words_acc [] (line D))) as H1.
  pose proof (broad_shl_words (line D) []) as H2. cbn [length] in *. lia.
Qed.

Lemma broad_join_len : forall ws, Z.of_nat (length (join_sp ws)) <= sup_host_setting_len ws.
Proof.
  induction ws as [|w ws IH]; [cbv; discriminate|]. rewrite broad_shl_cons.
  destruct ws as [|w2 ws'].
  - change (join_sp [w]) with w. change (sup_host_setting_len []) with 0. lia.
  - change (join_sp (w :: w2 :: ws')) with (w ++ SPACE :: join_sp (w2 :: ws')).
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma broad_f2 : forall {X Y : Type} (Pr : X -> Y -> Prop) l1 l2, length l1 = length l2 ->
  (forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> Pr x y) -> Forall2 Pr l1 l2.
Proof.
  intros X Y Pr l1; induction l1 as [|x l1 IH]; intros [|y l2] HL HP; cbn [length] in HL; try discriminate HL.
  - constructor.
  - constructor; [exact (HP 0%nat x y eq_refl eq_refl)|]. apply IH; [lia|].
    intros i x' y' E1 E2. exact (HP (S i) x' y' E1 E2).
Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Definition broad_vpost (K : Z) (L : layout) (A : astate) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (b : sbound) (sizes : list Z) (R' : rstate) (Q : bvmap 5 word -> Prop) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' rg' mem' md' O',
    c' = mkCfg (@mkst fx' rg' (getr rg 1) mem' (seg_rom rsegs)) md' /\
    RecKindB.fp_kept fx fx' /\
    RecKindB.call_post_rec B MR K L A rg mem md RecKindB.rec_area (fun a => In a (map fst O)) L' A' rg' mem' md' /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ RecKindB.owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    ro_agree (ms_segs B) mem' /\ st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (RecKindB.sb_mallocs b sizes) /\ Q rg'.

Lemma broad_call_v : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret sizes R' Q P,
  @vr_state fx _ B API S rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  getr rg 1 = Z_to_bv 64 ret -> 0 <= K <= 14336 ->
  (k1 + length sizes <= 32)%nat -> Forall (fun n => 0 <= n <= 8194) sizes ->
  SR rsegs c (broad_vpost K L1 A1 rg mem1 md1 O1 (sb_n (s_b S) k1) sizes R' Q) ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' c',
     @vr_state fx' _ B API S rg' ret mem' md' L' A' R' O' (k1 + length sizes) qv xq jk c' ->
     Q rg' -> regs_preserved rg rg' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret sizes R' Q P HST E1 HK HKS HSZ HSR KONT.
  pose proof (vf_segs B API HF) as SEGS.
  eapply SR_bind; [exact HSR|].
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & -> & FPK & POST & REC & OWN & BLK & OK & RO & INIT & RLEN
    & RES & HQ).
  pose proof HST as (_ & FPK0 & VR & H & FR & GQ & GW).
  pose proof POST as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _).
  pose proof (vregs_sp B API S HS rg VR) as SPR.
  pose proof (frame_keep B API HF S HS K rg mem1 mem' L1 A1 L' A' md1 md' RecKindB.rec_area HM1 HM' SPR
    rec_area_low HFR) as KP.
  pose proof (gq_keep B API HF S HS K rg mem1 mem' L1 A1 L' A' md1 md' RecKindB.rec_area HM1 HM' SPR HK
    rec_area_gq HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  assert (HQX : match xq with
                | Some (q, nq, t) => bytes_at rsegs mem' q (t ++ [Z_to_bv 8 0]) /\ Z.of_nat (length t) + 1 <= nq
                | None => True
                end).
  { pose proof (h_q B API S _ _ _ _ _ _ _ _ H) as HQ1.
    pose proof (h_t B API S _ _ _ _ _ _ _ _ H) as T.
    destruct xq as [[[q nq] t]|]; [|exact I].
    destruct HQ1 as [Hb Hl]. split; [|exact Hl].
    destruct (t_x B API S _ _ _ _ _ _ _ _ T (q, nq) (or_intror (or_intror (or_introl eq_refl)))) as [Hin Hno].
    assert (Hno' : ~ In (q, nq) O1) by (intros Ho; apply Hno; apply in_map_iff; exists (q, nq); split; [reflexivity | exact Ho]).
    destruct (ok_surv B L1 A1 mem1 L' A' mem' O1 q nq OK Hin Hno') as [_ KB].
    apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite <- SEGS. apply KB. lia. }
  apply (KONT fx' rg' mem' md' L' A' O'); [| exact HQ | exact HPR].
  split; [rewrite E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { apply (heap_step_stub B API HF S HS rg mem1 md1 L1 A1 R1 O1 k1 xq K L' A' rg' mem' md' R' O' [] xq
      (k1 + length sizes) H SPR HK POST REC OWN).
    - intros pn Hin. destruct (BLK pn Hin) as [X|X]; [left; exact X | right; left; exact X].
    - exact OK.
    - exact RO.
    - exact INIT.
    - exact RLEN.
    - exact (st_res B API S HS A' k1 sizes HKS HSZ RES).
    - exact HKS.
    - rewrite app_nil_r. reflexivity.
    - intros pn [].
    - constructor.
    - exact HQX. }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

End V.

Lemma broad_k1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17ae0) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x16114) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17ad8) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Lemma broad_k2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x17af4) sp gp tp t0 t1 t2 s0 s1 s0 (Z_to_bv 64 (bv_unsigned sp + 8)) s3 a3 a4 a5 a6 a7
                     s2 s3 a0 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x161a0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17ae0) fc None m (seg_rom rsegs)).
Proof. intros. do 5 zstep. apply evt_done. reflexivity. Qed.

Lemma k_j17af4 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17974) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17af4) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis DB : forall f : YK11.FPState, @sup_broadcast_contract f rc B API.
Hypothesis DH : forall f : YK11.FPState, @sup_host_setting_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_broad : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RBroad) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RBroad -> toks D <> [] -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  getr rg 19 = verbs_receive_disp.ntokw (toks D) ->
  join_k B API S 0x17974 20 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT NE N21 HK N19 JOIN.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  assert (LT1 : (1 <= length (toks D))%nat) by (destruct (toks D); [contradiction | cbn [length]; lia]).
  pose proof (ok_nD B API S HS) as OND. pose proof (ok_n8 B API S HS) as ON8.
  assert (LL : Z.of_nat (length (line D)) <= 8192) by (pose proof (verbs_receive_route.line_len D); lia).
  pose proof (sp_facts B API S HS) as (_ & _ & SP16 & SPF).
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RBroad) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply broad_k1. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 HQ X MK. cbv beta in HQ. injection HQ as ER EP. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK 0x16114 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  assert (E1 : getr rg' 1 = Z_to_bv 64 0x17ae0) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
  assert (E10 : getr rg' 10 = Z_to_bv 64 (s_lb S)).
  { rewrite (getr_of_eqv _ _ 10 X eq_refl). destruct VR as (_ & _ & _ & V8 & _). exact V8. }
  assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17ae0)) by (apply bv_eq; vm_compute; reflexivity).
  assert (KB : 0 <= SUP_BROADCAST_K <= 14336) by (unfold SUP_BROADCAST_K; lia).
  destruct (vs_pre B API HF S HS rg' 0x16114 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_BROADCAST_K 0x17ae0
              HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
  pose proof (st_line_arg B API HF S HS rg' 0x16114 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ SUP_BROADCAST_K HST1 KB) as SL.
  assert (LT : (length (snd (sup_broadcast_m R1 (line D))) <= 28)%nat).
  { unfold sup_broadcast_m. apply broad_text_len. exact (rep_code _ _ _ _ _ _ REC). }
  assert (HSZ : Forall (fun n => 0 <= n <= 8194) (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D))))).
  { unfold sup_broadcast_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
  assert (HKS : (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))) <= 32)%nat) by (unfold sup_broadcast_sizes; cbn [length]; lia).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
  pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
  assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D))))) <=
                sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))))).
  { destruct (sb_mallocs_fields (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
    rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
    unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_broadcast_sizes. cbn [length]. lia. }
  apply (call_ans B API HF S HS rg' 0x16114 mem2 md1 L1 A1 R1 O1 k1 qv jk _ SUP_BROADCAST_K 0x17ae0 (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))) (sup_broadcast_m R1 (line D)) P HST1 E1 KB HKS HSZ).
  { eapply SR_mono.
    { pose proof (DB f L1 A1 rg' mem2 md1 (s_lb S) (line D) R1 O1 (sb_n (s_b S) k1) PRE E10
                    ltac:(rewrite SPR; exact SL) REC RO FZ F18 RES ROOM) as C.
      rewrite SEGS in C. unfold SUP_BROADCAST in C. exact C. }
    intros c'' HR.
    exact (ans_of_ns B API HF SUP_BROADCAST_K (sup_broadcast_m R1 (line D)) (sup_broadcast_sizes (line D)) L1 A1 rg' mem2 md1 O1 (sb_n (s_b S) k1) c'' HR CAP). }
  intros f2 rg2 mem3 md3 La2 Aa2 O2 q c2 HST2 E10q HP2.
  pose proof HST2 as (_ & _ & VR2 & _).
  eapply (ka_nw B API HF S HS rg2 0x17ae0 mem3 md3 La2 Aa2 _ O2 _ qv _ jk c2 _ P HST2).
  { unfold Regs6ss.mkR_of. apply broad_k2. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R3 pc3 rg3 mem4 HQ3 X3 MK3. cbv beta in HQ3. injection HQ3 as ER EP. subst R3 pc3.
  assert (G2 : getr rg3 2 = getr rg2 2) by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); reflexivity).
  assert (G3 : getr rg3 3 = getr rg2 3) by (rewrite (getr_of_eqv _ _ 3 X3 eq_refl); reflexivity).
  assert (G4 : getr rg3 4 = getr rg2 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); reflexivity).
  assert (G8 : getr rg3 8 = getr rg2 8) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); reflexivity).
  assert (G9 : getr rg3 9 = getr rg2 9) by (rewrite (getr_of_eqv _ _ 9 X3 eq_refl); reflexivity).
  assert (G18 : getr rg3 18 = getr rg2 18) by (rewrite (getr_of_eqv _ _ 18 X3 eq_refl); reflexivity).
  assert (G21 : getr rg3 21 = getr rg2 21) by (rewrite (getr_of_eqv _ _ 21 X3 eq_refl); reflexivity).
  assert (G25 : getr rg3 25 = getr rg2 25) by (rewrite (getr_of_eqv _ _ 25 X3 eq_refl); reflexivity).
  assert (G26 : getr rg3 26 = getr rg2 26) by (rewrite (getr_of_eqv _ _ 26 X3 eq_refl); reflexivity).
  assert (G27 : getr rg3 27 = getr rg2 27) by (rewrite (getr_of_eqv _ _ 27 X3 eq_refl); reflexivity).
  assert (G19 : getr rg3 19 = getr rg2 19) by (rewrite (getr_of_eqv _ _ 19 X3 eq_refl); reflexivity).
  assert (G20 : getr rg3 20 = getr rg2 10) by (rewrite (getr_of_eqv _ _ 20 X3 eq_refl); reflexivity).
  assert (VR3 : vregs S rg3).
  { destruct VR2 as (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27).
    split; [rewrite G2; exact V2|]. split; [rewrite G3; exact V3|]. split; [rewrite G4; exact V4|].
    split; [rewrite G8; exact V8|]. split; [rewrite G9; exact V9|]. split; [rewrite G25; exact V25|].
    split; [rewrite G26; exact V26|]. rewrite G27; exact V27. }
  pose proof (MK3 0x161a0 eq_refl VR3) as HST3.
  assert (E1' : getr rg3 1 = Z_to_bv 64 0x17af4) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); reflexivity).
  assert (E10' : getr rg3 10 = Z_to_bv 64 (s_lb S)).
  { rewrite (getr_of_eqv _ _ 10 X3 eq_refl). destruct VR2 as (_ & _ & _ & V8 & _). exact V8. }
  assert (SP2' : bv_unsigned (reg_get rg2 2) = s_spf S).
  { destruct VR2 as (V2 & _). change (reg_get rg2 2) with (getr rg2 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (E11' : getr rg3 11 = Z_to_bv 64 (s_spf S + 8)).
  { rewrite (getr_of_eqv _ _ 11 X3 eq_refl). rewrite <- SP2'. reflexivity. }
  assert (E12' : getr rg3 12 = Z_to_bv 64 (Z.of_nat (length (toks D)))).
  { rewrite (getr_of_eqv _ _ 12 X3 eq_refl). transitivity (getr rg2 19); [reflexivity|].
    exact (eq_trans (HP2 19 ltac:(unfold callee_saved; lia)) (eq_trans (PR 19 ltac:(unfold callee_saved; lia)) N19)). }
  assert (RET' : YK0s.ret_ok (Z_to_bv 64 0x17af4)) by (apply bv_eq; vm_compute; reflexivity).
  assert (KB' : 0 <= SUP_HOST_SETTING_K <= 14336) by (unfold SUP_HOST_SETTING_K; lia).
  destruct (vs_pre B API HF S HS rg3 0x161a0 mem4 md3 La2 Aa2 _ O2 _ qv _ jk _ SUP_HOST_SETTING_K 0x17af4
              HST3 E1' RET' KB') as (PRE' & SPR' & FZ' & F18' & RO' & REC' & HM' & SH').
  pose proof (st_line_arg B API HF S HS rg3 0x161a0 mem4 md3 La2 Aa2 _ O2 _ qv _ jk _ SUP_HOST_SETTING_K HST3 KB') as SL'.
  pose proof HST3 as (_ & _ & _ & _ & FR3 & _).
  destruct FR3 as (_ & _ & FB3).
  assert (BY : bytes_at (ms_segs B) mem4 (s_spf S + 8)
                 (concat (map (fun p => le8 (Z_to_bv 64 p)) (map bv_unsigned (s_ps S))))).
  { rewrite SEGS. rewrite map_map.
    replace (map (fun x : word => le8 (Z_to_bv 64 (bv_unsigned x))) (s_ps S)) with (map le8 (s_ps S)); [exact FB3|].
    apply map_ext. intros p. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (F2 : Forall2 (fun p w => RecKindB.str_arg B La2 Aa2 O2 (spZ rg3) SUP_HOST_SETTING_K mem4 p (Some w))
                 (map bv_unsigned (s_ps S)) (toks D)).
  { apply broad_f2; [rewrite length_map; exact LPT|].
    intros i x w Ex Ew. rewrite nth_error_map in Ex.
    destruct (nth_error (s_ps S) i) as [p|] eqn:Ep; cbn in Ex; [|discriminate Ex]. injection Ex as <-.
    rewrite SPR'. exact (st_tok_arg B API HF S HS rg3 0x161a0 mem4 md3 La2 Aa2 _ O2 _ qv _ jk _ SUP_HOST_SETTING_K i p w HST3 KB' Ep Ew). }
  assert (RAX : forall a, s_spf S + 8 <= a < s_spf S + 8 + 8 * Z.of_nat (length (toks D)) -> ~ RecKindB.rec_area a).
  { intros a Ha HRA. unfold RecKindB.rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in HRA. unfold s_spf, VR_K in *. lia. }
  pose proof (broad_shl_toks D) as SHL. pose proof (broad_join_len (toks D)) as JL.
  pose proof (dec_length (Z.of_nat (length (toks D))) ltac:(lia)) as DL.
  assert (HSZ' : Forall (fun n => 0 <= n <= 8194) (sup_host_setting_sizes (line D) (toks D))).
  { unfold sup_host_setting_sizes. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
  assert (HKS' : (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))) + length (sup_host_setting_sizes (line D) (toks D)) <= 32)%nat)
    by (unfold sup_broadcast_sizes, sup_host_setting_sizes; cbn [length]; lia).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST3))))) as (RES' & _).
  pose proof (st_room B API S HS (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D))))) _ (LMAX + 2) HKS' HSZ' ltac:(unfold LMAX; lia)) as ROOM'.
  assert (CAP' : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))))) (sup_host_setting_sizes (line D) (toks D))) <=
                 sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))))) (sup_host_setting_sizes (line D) (toks D)))).
  { destruct (sb_mallocs_fields (sup_host_setting_sizes (line D) (toks D)) (sb_n (s_b S) (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D))))))) as (F1 & _ & F3).
    rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
    unfold sb_n. cbn [sb_live sb_cap] in *. unfold sup_broadcast_sizes, sup_host_setting_sizes. cbn [length]. lia. }
  apply (broad_call_v B API HF S HS rg3 0x161a0 mem4 md3 La2 Aa2 _ O2 _ qv _ jk _ SUP_HOST_SETTING_K 0x17af4 (sup_host_setting_sizes (line D) (toks D))
           (sup_host_setting_m (fst (sup_broadcast_m R1 (line D))) (line D) (toks D)) (fun _ => True) P HST3 E1' KB' HKS' HSZ').
  { eapply SR_mono.
    { pose proof (DH f2 La2 Aa2 rg3 mem4 md3 (s_lb S) (s_spf S + 8) (map bv_unsigned (s_ps S)) (line D) (toks D)
                    (fst (sup_broadcast_m R1 (line D))) O2 (sb_n (s_b S) (k1 + length (sup_broadcast_sizes (line D) (snd (sup_broadcast_m R1 (line D)))))) PRE' E10' E11' E12' ltac:(lia)
                    ltac:(rewrite SPR'; exact SL') ltac:(unfold s_spf in *; lia) ltac:(unfold s_spf in *; Z.div_mod_to_equations; lia)
                    BY ltac:(right; rewrite SPR'; lia) ltac:(left; rewrite SPR'; unfold s_spf in *; lia)
                    RAX
                    F2 ltac:(unfold LMAX; lia) REC' RO' FZ' F18' RES' ROOM') as C.
      rewrite SEGS in C. unfold SUP_HOST_SETTING in C. exact C. }
    intros c'' (fxX & LX & AX & rgX & memX & mdX & OX & E & FPK & POST & REC3 & OWN & BLK & OK & RO3 & _ & INIT & RLEN
      & LE & RS).
    exists fxX, LX, AX, rgX, memX, mdX, OX.
    split; [rewrite SEGS in E; exact E|]. split; [exact FPK|]. split; [exact POST|]. split; [exact REC3|].
    split; [exact OWN|]. split; [exact BLK|]. split; [exact OK|]. split; [exact RO3|]. split; [exact INIT|].
    split; [exact RLEN|]. split; [exact (RecKindB.res_ok_slots_le AX _ _ LE CAP' RS) | exact I]. }
  intros f3 rg4 mem5 md5 La3 Aa3 O3 c3 HST4 _ HP4.
  pose proof HST4 as (_ & _ & VR4 & _).
  eapply (ka_nw B API HF S HS rg4 0x17af4 mem5 md5 La3 Aa3 _ O3 _ qv _ jk c3 _ P HST4 (k_j17af4 _ _ _ _)).
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R5 pc5 rg5 mem6 HQ5 X5 MK5. cbv beta in HQ5. injection HQ5 as ER EP. subst R5 pc5.
  pose proof (getr_eqv_of rg4 rg5 X5) as GE.
  eapply JOIN. exists false.
  split; [apply MK5; [reflexivity | apply (vregs_pres S rg4 rg5 VR4); intros r _; apply GE]|].
  split.
  { exact (eq_trans (GE _) (eq_trans (HP4 20 ltac:(unfold callee_saved; lia)) (eq_trans G20 E10q))). }
  split.
  { exact (eq_trans (GE _) (eq_trans (HP4 18 ltac:(unfold callee_saved; lia)) (eq_trans G18 (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia)))))). }
  split.
  { intros _. exact (eq_trans (GE _) (eq_trans (HP4 21 ltac:(unfold callee_saved; lia)) (eq_trans G21 (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia)))))). }
  split.
  { destruct (toks D) as [|v args] eqn:TK; [contradiction|]. rewrite RT. cbn [plan_at].
    unfold VerbsRun.run_step. destruct (sup_broadcast_m R1 (line D)); reflexivity. }
  unfold sup_broadcast_sizes, sup_host_setting_sizes. cbn [length]. lia.
Qed.

End R.
