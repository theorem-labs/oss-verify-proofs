(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptMorphSeqA.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23Memset V23LeptStrlenH V23LeptMorphSeqA V23ExecUb.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExecB.

Definition STOPS : list Z := [1107680; 1107992; 453468]%Z.
Definition STOPS2 : list Z := [1107680; 1107992; 453468; 1174112; 1173204]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition MSEQH_WIN : Z := 4096.

Lemma mh_cs_agree : forall (l : list reg) regs r1, Forall (fun r => (10 <= bv_unsigned r <= 17)%Z) l ->
  regs_agree (fun r => In r l) regs r1 -> cs_kept regs r1.
Proof.
  intros l regs r1 HL H r CS. apply H. intros Hin.
  pose proof (proj1 (Forall_forall _ l) HL r Hin) as X. cbv beta in X.
  unfold callee_saved in CS.
  destruct CS as [E|[E|[E|[E|[E|E]]]]];
    [ rewrite E in X; assert (Hv : bv_unsigned (2%bv : reg) = 2%Z) by reflexivity; lia
    | rewrite E in X; assert (Hv : bv_unsigned (3%bv : reg) = 3%Z) by reflexivity; lia
    | rewrite E in X; assert (Hv : bv_unsigned (4%bv : reg) = 4%Z) by reflexivity; lia
    | rewrite E in X; assert (Hv : bv_unsigned (8%bv : reg) = 8%Z) by reflexivity; lia
    | rewrite E in X; assert (Hv : bv_unsigned (9%bv : reg) = 9%Z) by reflexivity; lia
    | lia ].
Qed.
Lemma mh_cs_sl : forall regs r1, regs_agree (fun r => In r sl_clob) regs r1 -> cs_kept regs r1.
Proof.
  intros regs r1 H. apply (mh_cs_agree sl_clob regs r1); [|exact H]. unfold sl_clob.
  repeat apply Forall_cons; try apply Forall_nil; vm_compute; split; intro X; discriminate X.
Qed.
Lemma mh_cs_ms : forall regs r1, regs_agree (fun r => In r memset_clob) regs r1 -> cs_kept regs r1.
Proof.
  intros regs r1 H. apply (mh_cs_agree memset_clob regs r1); [|exact H]. unfold memset_clob.
  repeat apply Forall_cons; try apply Forall_nil; vm_compute; split; intro X; discriminate X.
Qed.
Lemma mh_sltu_self : forall p : Z, (0 <= p < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 p) (Z_to_bv 64 p) = Z_to_bv 64 0.
Proof. intros p Hp. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite Z.ltb_irrefl. reflexivity. Qed.
Lemma mh_sltu_addge : forall p k : Z, (0 <= p)%Z -> (0 <= k)%Z -> (p + k < 2 ^ 64)%Z ->
  alu64 ALU_SLTU (Z_to_bv 64 (p + k)) (Z_to_bv 64 p) = Z_to_bv 64 0.
Proof. intros p k Hp Hk Hpk. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite (proj2 (Z.ltb_ge (p + k) p)) by lia. reflexivity. Qed.
Ltac mh_sc_hook :=
  repeat match goal with
         | |- context [alu64 ALU_SLTU (Z_to_bv 64 ?p) (Z_to_bv 64 ?p)] => rewrite (mh_sltu_self p) by lia
         | |- context [alu64 ALU_SLTU (Z_to_bv 64 (?p + ?k)) (Z_to_bv 64 ?p)] => rewrite (mh_sltu_addge p k) by lia
         end;
  v23_and0; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity.
#[local] Ltac exB_sc_hook ::= first [ mcs_sc_hook | v23_sc_hook | mh_sc_hook ].
Ltac mh_at_branch ST :=
  lazymatch type of ST with
  | ex_st ?segs _ _ _ _ _ ?pc _ _ =>
      let d := eval vm_compute in (match fetch_word segs (Z_to_bv 64 pc) with Some w => decode_any w | None => None end) in
      lazymatch d with Some (Branch _ _ _ _, _) => idtac | _ => fail end
  end.
Ltac mh_loop rounds fuel stops dirs fdef HK ST FZ :=
  first [ exb_at_stop stops ST | exb_at_jalr ST
        | (mh_at_branch ST; lazymatch dirs with ?d :: ?rest =>
             exb_autoS rounds fuel stops (SCR [d] [] []) HK ST ltac:(fun _ => mh_loop rounds fuel stops rest fdef HK ST FZ) end)
        | (exb_fstep fdef HK ST FZ; exb_norm ST;
           first [ exb_at_stop stops ST | exb_autoS rounds fuel stops (SCR [] [] []) HK ST ltac:(fun _ => mh_loop rounds fuel stops dirs fdef HK ST FZ) ]) ].
Ltac mh_drive rounds fuel stops dirs fdef HK ST FZ :=
  exb_autoS rounds fuel stops (SCR [] [] []) HK ST ltac:(fun _ => mh_loop rounds fuel stops dirs fdef HK ST FZ).

Lemma mseq_head : forall (fx : FPState) C A m md regs (s pixs : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + MSEQH_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 98147 -> getr regs 12 = Z_to_bv 64 0 -> (0 <= pixs < 2 ^ 64)%Z -> (pixs <> 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (7 <= kR)%Z -> (7 * 2 ^ 17 <= bR)%Z ->
  (forall A' m' vm' regs' (sa arr s1 s2 : Z),
     W C A' m' (with_vmmaps vm' md) -> sub_live A A' -> POSTM C A s m m' ->
     aroom A' vm' (kR - 7) (bR - 7 * 2 ^ 17) ->
     (forall q : word, ~ In q [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] -> live A' q = live A q) ->
     getr regs' 1 = Z_to_bv 64 681724 -> getr regs' 2 = Z_to_bv 64 (s + -448) -> getr regs' 3 = getr regs 3 -> getr regs' 4 = Z_to_bv 64 1278416 ->
     getr regs' 10 = Z_to_bv 64 0 -> getr regs' 11 = Z_to_bv 64 pixs -> getr regs' 8 = Z_to_bv 64 0 -> getr regs' 9 = Z_to_bv 64 98147 ->
     getr regs' 18 = Z_to_bv 64 2 -> getr regs' 19 = Z_to_bv 64 pixs -> getr regs' 20 = Z_to_bv 64 sa ->
     live A' (Z_to_bv 64 sa) = Some 24%Z -> live A (Z_to_bv 64 sa) = None -> live (c_A0 C) (Z_to_bv 64 sa) = None -> (0 <= sa < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 arr) = Some 400%Z -> live A (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 s1) = Some 6%Z -> live A (Z_to_bv 64 s1) = None -> live (c_A0 C) (Z_to_bv 64 s1) = None -> (0 <= s1 < 2 ^ 64)%Z ->
     live A' (Z_to_bv 64 s2) = Some 7%Z -> live A (Z_to_bv 64 s2) = None -> live (c_A0 C) (Z_to_bv 64 s2) = None -> (0 <= s2 < 2 ^ 64)%Z ->
     Z_to_bv 64 sa <> Z_to_bv 64 arr ->
     Z_to_bv 64 sa <> Z_to_bv 64 s1 ->
     Z_to_bv 64 arr <> Z_to_bv 64 s1 ->
     Z_to_bv 64 sa <> Z_to_bv 64 s2 ->
     Z_to_bv 64 arr <> Z_to_bv 64 s2 ->
     Z_to_bv 64 s1 <> Z_to_bv 64 s2 ->
     rdn SEGS m' (Z_to_bv 64 (sa + 0)) 4 = Some (Z_to_le_bytes 4 50) ->
     rdn SEGS m' (Z_to_bv 64 (sa + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
     rdn SEGS m' (Z_to_bv 64 (sa + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
     rdn SEGS m' (Z_to_bv 64 (sa + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 s1) ->
     rdn SEGS m' (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 s2) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 0)) 1 = Some (Z_to_le_bytes 1 99) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 1)) 1 = Some (Z_to_le_bytes 1 49) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 2)) 1 = Some (Z_to_le_bytes 1 46) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 3)) 1 = Some (Z_to_le_bytes 1 56) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 4)) 1 = Some (Z_to_le_bytes 1 32) ->
     rdn SEGS m' (Z_to_bv 64 (s1 + 5)) 1 = Some (Z_to_le_bytes 1 0) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 0)) 1 = Some (Z_to_le_bytes 1 32) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 1)) 1 = Some (Z_to_le_bytes 1 99) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 2)) 1 = Some (Z_to_le_bytes 1 51) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 3)) 1 = Some (Z_to_le_bytes 1 48) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 4)) 1 = Some (Z_to_le_bytes 1 46) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 5)) 1 = Some (Z_to_le_bytes 1 49) ->
     rdn SEGS m' (Z_to_bv 64 (s2 + 6)) 1 = Some (Z_to_le_bytes 1 0) ->
     rdn SEGS m' (Z_to_bv 64 (s + -424)) 8 = Some (Z_to_le_bytes 8 sa) ->
     rdn SEGS m' (Z_to_bv 64 (s + -416)) 8 = Some (Z_to_le_bytes 8 0) ->
     rdn SEGS m' (Z_to_bv 64 (s + -376)) 4 = Some (Z_to_le_bytes 4 0) ->
     rdn SEGS m' (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -80)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -88)) 8 = Some (word_to_le_bytes 8 (getr regs 25)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -96)) 8 = Some (word_to_le_bytes 8 (getr regs 26)) ->
     rdn SEGS m' (Z_to_bv 64 (s + -104)) 8 = Some (word_to_le_bytes 8 (getr regs 27)) ->
     realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 453468) m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 681532) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs S CK HW0 H2 Hs16 Hlo Hhi H4 H10 H11 H12 Rpixs NZpixs kR bR RM0 HkR HbR HC.
  unfold MSEQH_WIN in *.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  replace kR with (kR - 0)%Z in RM0 by lia. replace bR with (bR - 0 * 2 ^ 17)%Z in RM0 by lia.
  pose (valsI := @nil word).
  pose proof (fun (q : word) (_ : ~ In q []) => eq_refl (live A0 q)) as LDEL0.
  assert (GLO1 : (c_top C - LSTK <= s - 4096)%Z) by lia.
  assert (GLO2 : (s - 4096 + Z.of_nat (Z.to_nat 4096) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4096 <= s)%Z) by lia.
  pose proof (W_sok_win C A0 m0 _ (s - 4096) (Z.to_nat 4096) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; exW_canary SEGS 1410112 m0]) (EVar 35) (EVar 32) (exW_canary SEGS 1410112 m0) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 409600 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 64 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  pose proof (mcs_canary_eq C A0 m0 _ CK HW0) as CEQ0.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 4096 [] CK HW0 SUB0 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  pose proof (alloc_margin_small (1 * 24) ltac:(exW_cmp)) as MG0.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_0 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A0 M0 _ Rc0 1 24 (kR - 0) (bR - 0 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs0 Q10_0 Q11_0 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q4_0 Q2_0 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A1 m1 vm1 r1 res0 HW1 Hres0 CSx0 Hnz0 Fsax Lo0 F0sa LEQ0 ZERO_sa ALsa TOP0 PMc0 RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  assert (Eres0 : res0 = Z_to_bv 64 (u res0)) by (symmetry; apply zbv_self).
  pose proof (u64_range res0) as RRsa. set (sa := u res0) in *. clearbody sa. rewrite Eres0 in Hres0, Fsax, Lo0, F0sa, LEQ0, ZERO_sa. clear Eres0.
  change (1 * 24)%Z with 24%Z in *.
  assert (NZsa : (1 <= sa < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A1 m1 _ sa 24 CK HW1 Lo0 RRsa ltac:(lia)) as (GLsa1 & GLsa2 & GLsa3).
  pose proof (exW_blk_img_apart_h2 C A1 m1 _ sa 24 CK HW1 Lo0 RRsa eq_refl eq_refl) as IMGAPsa. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsa.
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 4096 sa 24 CK HW1 Lo0 eq_refl RRsa GLO1) as WAPsa.
  assert (Fsa : live A0 (Z_to_bv 64 sa) = None).
  { destruct (live A0 (Z_to_bv 64 sa)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB0 _ _ EE) as XX. first [discriminate Fsax | (rewrite Fsax in XX; discriminate XX)]. }
  pose proof Lo0 as Lsa_a1.
  assert (SUB1 : sub_live A0 A1).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sa) by (intros ->; rewrite Fsa in Lq; discriminate Lq). rewrite (LEQ0 q NEq). exact (SUB0 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 sa :: [])) => eq_trans (LEQ0 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL0 q (fun XX => Hq (or_intror XX)))) as LDEL1.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C A0 A0 _ _ _ SUB0).
    apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  replace (kR - 0 - 1)%Z with (kR - 1)%Z in RM1 by lia. rewrite MG0 in RM1. replace (bR - 0 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 1 * 2 ^ 17)%Z in RM1 by lia.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF0 4096 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk0 kk' EQ) as HKk0_; clear EQ HKk0; rename HKk0_ into HKk0 end.
  pose proof (regs_ok_agree 36%nat E0 (ex_envL vals0 r1 [sa; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [sa; exW_canary SEGS 1410112 m1] 36%nat ltac:(vm_cast_no_check (eq_refl 36%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [sa; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 36%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  try rewrite (fr_denot_agree 36%nat E0 (ex_envL vals0 r1 [sa; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 68) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 PM0 HW0 PMc0 CS0 OFF0 BS0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 SUB0 RM0 MG0 TOP0 LEQ0 Hnz0 Fsax Lo0 LDEL0 .
  repeat match goal with H : getr Rc0 _ = _ |- _ => clear H end.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn1 sr' EQ : regs_ok EE sr' RR) as HRn1_; clear EQ HRn1; rename HRn1_ into HRn1 end.
  pose proof (exW_kn_blk SEGS C A1 m1 _ (ex_envL vals0 r1 [sa; exW_canary SEGS 1410112 m1]) (EVar 68) (EVar 32) sa 24 s 4096 65536 1347584 p16_segs CK HW1 Lsa_a1 RRsa eq_refl eq_refl eq_refl RS ALsa ZERO_sa WAPsa IMGAPsa) as HKb1.
  pose proof (W_sok_win C A1 m1 _ (s - 4096) (Z.to_nat 4096) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [sa; exW_canary SEGS 1410112 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [sa; exW_canary SEGS 1410112 m1]) (EVar 69) (EVar 32) (exW_canary SEGS 1410112 m1) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  pose proof (mcs_canary_eq C A1 m1 _ CK HW1) as CEQ1.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_sa.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 4096 [(EVar 68, sa, 24%Z)] CK HW1 SUB1 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a1 (conj Fsa F0sa))))|].
    constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (68%nat, sa)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  pose proof (alloc_margin_small (50 * 8) ltac:(exW_cmp)) as MG1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_1 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A1 M1 _ Rc1 50 8 (kR - 1) (bR - 1 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs1 Q10_1 Q11_1 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_1
             ltac:(red; apply bv_eq; reflexivity) Q4_1 Q2_1 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A2 m2 vm2 r2 res1 HW2 Hres1 CSx1 Hnz1 Farrx Lo1 F0arr LEQ1 ZERO_arr ALarr TOP1 PMc1 RM2.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  assert (Eres1 : res1 = Z_to_bv 64 (u res1)) by (symmetry; apply zbv_self).
  pose proof (u64_range res1) as RRarr. set (arr := u res1) in *. clearbody arr. rewrite Eres1 in Hres1, Farrx, Lo1, F0arr, LEQ1, ZERO_arr. clear Eres1.
  change (50 * 8)%Z with 400%Z in *.
  assert (NZarr : (1 <= arr < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A2 m2 _ arr 400 CK HW2 Lo1 RRarr ltac:(lia)) as (GLarr1 & GLarr2 & GLarr3).
  pose proof (exW_blk_img_apart_h2 C A2 m2 _ arr 400 CK HW2 Lo1 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (exW_win_blk_apart_h C A2 m2 _ s 4096 arr 400 CK HW2 Lo1 eq_refl RRarr GLO1) as WAParr.
  assert (Farr : live A0 (Z_to_bv 64 arr) = None).
  { destruct (live A0 (Z_to_bv 64 arr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Farrx | (rewrite Farrx in XX; discriminate XX)]. }
  pose proof Lo1 as Larr_a2.
  assert (SUB2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ1 q NEq). exact (SUB1 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 arr :: [Z_to_bv 64 sa])) => eq_trans (LEQ1 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL1 q (fun XX => Hq (or_intror XX)))) as LDEL2.
  assert (NE_sa_arr : Z_to_bv 64 sa <> Z_to_bv 64 arr) by (intros EE; rewrite EE in Lsa_a1; rewrite Farrx in Lsa_a1; discriminate Lsa_a1).
  assert (Lsa_a2 : live A2 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ1 _ NE_sa_arr); exact Lsa_a1).
  pose proof (exW_blk_apart_h C A2 m2 _ sa arr 24 400 CK HW2 Lsa_a2 Larr_a2 NE_sa_arr RRsa RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_arr.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_sub C A0 A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  replace (kR - 1 - 1)%Z with (kR - 2)%Z in RM2 by lia. rewrite MG1 in RM2. replace (bR - 1 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 2 * 2 ^ 17)%Z in RM2 by lia.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z); (EVar 68, 0%Z, 24%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF1 4096 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A1 A1 M1 _ M1 m2 E1 (EVar 68) sa 24 CK HWs1 Lsa_a1 RRsa eq_refl (proj2 PMc1) Lsa_a1 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk1 kk' EQ) as HKk1_; clear EQ HKk1; rename HKk1_ into HKk1 end.
  pose proof (regs_ok_agree 70%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [arr; exW_canary SEGS 1410112 m2] 70%nat ltac:(vm_cast_no_check (eq_refl 70%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 70%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  try rewrite (fr_denot_agree 70%nat E1 (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 102) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 PM1 HW1 PMc1 CS1 OFF1 BS1 Q10_1 Q11_1 Q1_1 Q2_1 Q4_1 SUB1 RM1 MG1 TOP1 LEQ1 Hnz1 Farrx Lo1 LDEL1 Lsa_a1.
  repeat match goal with H : getr Rc1 _ = _ |- _ => clear H end.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn2 sr' EQ : regs_ok EE sr' RR) as HRn2_; clear EQ HRn2; rename HRn2_ into HRn2 end.
  pose proof (exW_kn_blk SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 102) (EVar 32) arr 400 s 4096 65536 1347584 p16_segs CK HW2 Larr_a2 RRarr eq_refl eq_refl eq_refl RS ALarr ZERO_arr WAParr IMGAParr) as HKb2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2) _ _ (ex_kdisj_apart SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2 (EVar 68) (EVar 102) sa arr 0 24 0 400 eq_refl eq_refl RRsa RRarr AP_sa_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) m2))) as HKd_sa_arr.
  pose proof (W_sok_win C A2 m2 _ (s - 4096) (Z.to_nat 4096) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [arr; exW_canary SEGS 1410112 m2]).
  pose proof (exW_kn_fixed SEGS C A2 m2 _ (ex_envL vals1 r2 [arr; exW_canary SEGS 1410112 m2]) (EVar 103) (EVar 32) (exW_canary SEGS 1410112 m2) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb2 (proj2 (Forall_app _ _ _) (conj HKd_sa_arr (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  pose proof (mcs_canary_eq C A2 m2 _ CK HW2) as CEQ2.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb2 HKd_sa_arr HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS (@nil bool) FDEF HK ST FZ.
  clear ZERO_arr.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A2 M2 (with_vmmaps vm2 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A2 A0 m2 _ E2 log2 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z)] CK HW2 SUB2 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a2 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a2 (conj Farr F0arr))))|].
    constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (13 * 1) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A2 M2 _ Rc2 13 1 (kR - 2) (bR - 2 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m3 vm3 r3 res2 HW3 Hres2 CSx2 Hnz2 Fcstrx Lo2 F0cstr LEQ2 ZERO_cstr ALcstr TOP2 PMc2 RM3.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRcstr. set (cstr := u res2) in *. clearbody cstr. rewrite Eres2 in Hres2, Fcstrx, Lo2, F0cstr, LEQ2, ZERO_cstr. clear Eres2.
  change (13 * 1)%Z with 13%Z in *.
  assert (NZcstr : (1 <= cstr < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A3 m3 _ cstr 13 CK HW3 Lo2 RRcstr ltac:(lia)) as (GLcstr1 & GLcstr2 & GLcstr3).
  pose proof (exW_blk_img_apart_h2 C A3 m3 _ cstr 13 CK HW3 Lo2 RRcstr eq_refl eq_refl) as IMGAPcstr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPcstr.
  pose proof (exW_win_blk_apart_h C A3 m3 _ s 4096 cstr 13 CK HW3 Lo2 eq_refl RRcstr GLO1) as WAPcstr.
  assert (Fcstr : live A0 (Z_to_bv 64 cstr) = None).
  { destruct (live A0 (Z_to_bv 64 cstr)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB2 _ _ EE) as XX. first [discriminate Fcstrx | (rewrite Fcstrx in XX; discriminate XX)]. }
  pose proof Lo2 as Lcstr_a3.
  assert (SUB3 : sub_live A0 A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 cstr) by (intros ->; rewrite Fcstr in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB2 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 cstr :: [Z_to_bv 64 arr; Z_to_bv 64 sa])) => eq_trans (LEQ2 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL2 q (fun XX => Hq (or_intror XX)))) as LDEL3.
  assert (NE_sa_cstr : Z_to_bv 64 sa <> Z_to_bv 64 cstr) by (intros EE; rewrite EE in Lsa_a2; rewrite Fcstrx in Lsa_a2; discriminate Lsa_a2).
  assert (Lsa_a3 : live A3 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ2 _ NE_sa_cstr); exact Lsa_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ sa cstr 24 13 CK HW3 Lsa_a3 Lcstr_a3 NE_sa_cstr RRsa RRcstr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_cstr.
  assert (NE_arr_cstr : Z_to_bv 64 arr <> Z_to_bv 64 cstr) by (intros EE; rewrite EE in Larr_a2; rewrite Fcstrx in Larr_a2; discriminate Larr_a2).
  assert (Larr_a3 : live A3 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ2 _ NE_arr_cstr); exact Larr_a2).
  pose proof (exW_blk_apart_h C A3 m3 _ arr cstr 400 13 CK HW3 Larr_a3 Lcstr_a3 NE_arr_cstr RRarr RRcstr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_cstr.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C A0 A2 _ _ _ SUB2).
    apply (POSTM_mono C A2 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  replace (kR - 2 - 1)%Z with (kR - 3)%Z in RM3 by lia. rewrite MG2 in RM3. replace (bR - 2 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 3 * 2 ^ 17)%Z in RM3 by lia.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF2 4096 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 68) sa 24 CK HWs2 Lsa_a2 RRsa eq_refl (proj2 PMc2) Lsa_a2 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A2 A2 M2 _ M2 m3 E2 (EVar 102) arr 400 CK HWs2 Larr_a2 RRarr eq_refl (proj2 PMc2) Larr_a2 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk2 kk' EQ) as HKk2_; clear EQ HKk2; rename HKk2_ into HKk2 end.
  pose proof (regs_ok_agree 104%nat E2 (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [cstr; exW_canary SEGS 1410112 m3] 104%nat ltac:(vm_cast_no_check (eq_refl 104%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 104%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  try rewrite (fr_denot_agree 104%nat E2 (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 136) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 PM2 HW2 PMc2 CS2 OFF2 BS2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 SUB2 RM2 MG2 TOP2 LEQ2 Hnz2 Fcstrx Lo2 LDEL2 Lsa_a2 Larr_a2.
  repeat match goal with H : getr Rc2 _ = _ |- _ => clear H end.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn3 sr' EQ : regs_ok EE sr' RR) as HRn3_; clear EQ HRn3; rename HRn3_ into HRn3 end.
  pose proof (exW_kn_blk SEGS C A3 m3 _ (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) (EVar 136) (EVar 32) cstr 13 s 4096 65536 1347584 p16_segs CK HW3 Lcstr_a3 RRcstr eq_refl eq_refl eq_refl RS ALcstr ZERO_cstr WAPcstr IMGAPcstr) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3 (EVar 68) (EVar 136) sa cstr 0 24 0 13 eq_refl eq_refl RRsa RRcstr AP_sa_cstr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3))) as HKd_sa_cstr.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3 (EVar 102) (EVar 136) arr cstr 0 400 0 13 eq_refl eq_refl RRarr RRcstr AP_arr_cstr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) m3))) as HKd_arr_cstr.
  pose proof (W_sok_win C A3 m3 _ (s - 4096) (Z.to_nat 4096) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [cstr; exW_canary SEGS 1410112 m3]).
  pose proof (exW_kn_fixed SEGS C A3 m3 _ (ex_envL vals2 r3 [cstr; exW_canary SEGS 1410112 m3]) (EVar 137) (EVar 32) (exW_canary SEGS 1410112 m3) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd_sa_cstr (proj2 (Forall_app _ _ _) (conj HKd_arr_cstr (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  pose proof (mcs_canary_eq C A3 m3 _ CK HW3) as CEQ3.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb3 HKd_sa_cstr HKd_arr_cstr HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_cstr.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A3 M3 (with_vmmaps vm3 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A3 A0 m3 _ E3 log3 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 136, cstr, 13%Z)] CK HW3 SUB3 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a3 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a3 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRcstr (conj Lcstr_a3 (conj Fcstr F0cstr))))|].
    constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r4 Q4_3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  pose proof (alloc_margin_small (6 * 1) ltac:(exW_cmp)) as MG3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_3 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A3 M3 _ Rc3 6 1 (kR - 3) (bR - 3 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs3 Q10_3 Q11_3 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_3
             ltac:(red; apply bv_eq; reflexivity) Q4_3 Q2_3 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m4 vm4 r4 res3 HW4 Hres3 CSx3 Hnz3 Fs1x Lo3 F0s1 LEQ3 ZERO_s1 ALs1 TOP3 PMc3 RM4.
  pose proof CSx3 as CS3. clear CSx3.
  rewrite with_vmmaps_twice in HW4 |- *.
  assert (Eres3 : res3 = Z_to_bv 64 (u res3)) by (symmetry; apply zbv_self).
  pose proof (u64_range res3) as RRs1. set (s1 := u res3) in *. clearbody s1. rewrite Eres3 in Hres3, Fs1x, Lo3, F0s1, LEQ3, ZERO_s1. clear Eres3.
  change (6 * 1)%Z with 6%Z in *.
  assert (NZs1 : (1 <= s1 < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A4 m4 _ s1 6 CK HW4 Lo3 RRs1 ltac:(lia)) as (GLs11 & GLs12 & GLs13).
  pose proof (exW_blk_img_apart_h2 C A4 m4 _ s1 6 CK HW4 Lo3 RRs1 eq_refl eq_refl) as IMGAPs1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPs1.
  pose proof (exW_win_blk_apart_h C A4 m4 _ s 4096 s1 6 CK HW4 Lo3 eq_refl RRs1 GLO1) as WAPs1.
  assert (Fs1 : live A0 (Z_to_bv 64 s1) = None).
  { destruct (live A0 (Z_to_bv 64 s1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB3 _ _ EE) as XX. first [discriminate Fs1x | (rewrite Fs1x in XX; discriminate XX)]. }
  pose proof Lo3 as Ls1_a4.
  assert (SUB4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 s1) by (intros ->; rewrite Fs1 in Lq; discriminate Lq). rewrite (LEQ3 q NEq). exact (SUB3 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 s1 :: [Z_to_bv 64 cstr; Z_to_bv 64 arr; Z_to_bv 64 sa])) => eq_trans (LEQ3 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL3 q (fun XX => Hq (or_intror XX)))) as LDEL4.
  assert (NE_sa_s1 : Z_to_bv 64 sa <> Z_to_bv 64 s1) by (intros EE; rewrite EE in Lsa_a3; rewrite Fs1x in Lsa_a3; discriminate Lsa_a3).
  assert (Lsa_a4 : live A4 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ3 _ NE_sa_s1); exact Lsa_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ sa s1 24 6 CK HW4 Lsa_a4 Ls1_a4 NE_sa_s1 RRsa RRs1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_s1.
  assert (NE_arr_s1 : Z_to_bv 64 arr <> Z_to_bv 64 s1) by (intros EE; rewrite EE in Larr_a3; rewrite Fs1x in Larr_a3; discriminate Larr_a3).
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ3 _ NE_arr_s1); exact Larr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ arr s1 400 6 CK HW4 Larr_a4 Ls1_a4 NE_arr_s1 RRarr RRs1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_s1.
  assert (NE_cstr_s1 : Z_to_bv 64 cstr <> Z_to_bv 64 s1) by (intros EE; rewrite EE in Lcstr_a3; rewrite Fs1x in Lcstr_a3; discriminate Lcstr_a3).
  assert (Lcstr_a4 : live A4 (Z_to_bv 64 cstr) = Some 13%Z) by (rewrite (LEQ3 _ NE_cstr_s1); exact Lcstr_a3).
  pose proof (exW_blk_apart_h C A4 m4 _ cstr s1 13 6 CK HW4 Lcstr_a4 Ls1_a4 NE_cstr_s1 RRcstr RRs1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_cstr_s1.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_sub C A0 A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  replace (kR - 3 - 1)%Z with (kR - 4)%Z in RM4 by lia. rewrite MG3 in RM4. replace (bR - 3 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 4 * 2 ^ 17)%Z in RM4 by lia.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 136, 0%Z, 13%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF3 4096 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 68) sa 24 CK HWs3 Lsa_a3 RRsa eq_refl (proj2 PMc3) Lsa_a3 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 102) arr 400 CK HWs3 Larr_a3 RRarr eq_refl (proj2 PMc3) Larr_a3 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A3 A3 M3 _ M3 m4 E3 (EVar 136) cstr 13 CK HWs3 Lcstr_a3 RRcstr eq_refl (proj2 PMc3) Lcstr_a3 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk3 kk' EQ) as HKk3_; clear EQ HKk3; rename HKk3_ into HKk3 end.
  pose proof (regs_ok_agree 138%nat E3 (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [s1; exW_canary SEGS 1410112 m4] 138%nat ltac:(vm_cast_no_check (eq_refl 138%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 138%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  try rewrite (fr_denot_agree 138%nat E3 (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 170) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 PM3 HW3 PMc3 CS3 OFF3 BS3 Q10_3 Q11_3 Q1_3 Q2_3 Q4_3 SUB3 RM3 MG3 TOP3 LEQ3 Hnz3 Fs1x Lo3 LDEL3 Lsa_a3 Larr_a3 Lcstr_a3.
  repeat match goal with H : getr Rc3 _ = _ |- _ => clear H end.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn4 sr' EQ : regs_ok EE sr' RR) as HRn4_; clear EQ HRn4; rename HRn4_ into HRn4 end.
  pose proof (exW_kn_blk SEGS C A4 m4 _ (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) (EVar 170) (EVar 32) s1 6 s 4096 65536 1347584 p16_segs CK HW4 Ls1_a4 RRs1 eq_refl eq_refl eq_refl RS ALs1 ZERO_s1 WAPs1 IMGAPs1) as HKb4.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4 (EVar 68) (EVar 170) sa s1 0 24 0 6 eq_refl eq_refl RRsa RRs1 AP_sa_s1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4))) as HKd_sa_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4 (EVar 102) (EVar 170) arr s1 0 400 0 6 eq_refl eq_refl RRarr RRs1 AP_arr_s1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4))) as HKd_arr_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4) _ _ (ex_kdisj_apart SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4 (EVar 136) (EVar 170) cstr s1 0 13 0 6 eq_refl eq_refl RRcstr RRs1 AP_cstr_s1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) m4))) as HKd_cstr_s1.
  pose proof (W_sok_win C A4 m4 _ (s - 4096) (Z.to_nat 4096) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [s1; exW_canary SEGS 1410112 m4]).
  pose proof (exW_kn_fixed SEGS C A4 m4 _ (ex_envL vals3 r4 [s1; exW_canary SEGS 1410112 m4]) (EVar 171) (EVar 32) (exW_canary SEGS 1410112 m4) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb4 (proj2 (Forall_app _ _ _) (conj HKd_sa_s1 (proj2 (Forall_app _ _ _) (conj HKd_arr_s1 (proj2 (Forall_app _ _ _) (conj HKd_cstr_s1 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  pose proof (mcs_canary_eq C A4 m4 _ CK HW4) as CEQ4.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb4 HKd_sa_s1 HKd_arr_s1 HKd_cstr_s1 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_s1.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A4 M4 (with_vmmaps vm4 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A4 A0 m4 _ E4 log4 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 136, cstr, 13%Z); (EVar 170, s1, 6%Z)] CK HW4 SUB4 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a4 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a4 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRcstr (conj Lcstr_a4 (conj Fcstr F0cstr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a4 (conj Fs1 F0s1))))|].
    constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  pose proof (alloc_margin_small (7 * 1) ltac:(exW_cmp)) as MG4.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_4 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A4 M4 _ Rc4 7 1 (kR - 4) (bR - 4 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs4 Q10_4 Q11_4 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_4
             ltac:(red; apply bv_eq; reflexivity) Q4_4 Q2_4 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A5 m5 vm5 r5 res4 HW5 Hres4 CSx4 Hnz4 Fs2x Lo4 F0s2 LEQ4 ZERO_s2 ALs2 TOP4 PMc4 RM5.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  assert (Eres4 : res4 = Z_to_bv 64 (u res4)) by (symmetry; apply zbv_self).
  pose proof (u64_range res4) as RRs2. set (s2 := u res4) in *. clearbody s2. rewrite Eres4 in Hres4, Fs2x, Lo4, F0s2, LEQ4, ZERO_s2. clear Eres4.
  change (7 * 1)%Z with 7%Z in *.
  assert (NZs2 : (1 <= s2 < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A5 m5 _ s2 7 CK HW5 Lo4 RRs2 ltac:(lia)) as (GLs21 & GLs22 & GLs23).
  pose proof (exW_blk_img_apart_h2 C A5 m5 _ s2 7 CK HW5 Lo4 RRs2 eq_refl eq_refl) as IMGAPs2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPs2.
  pose proof (exW_win_blk_apart_h C A5 m5 _ s 4096 s2 7 CK HW5 Lo4 eq_refl RRs2 GLO1) as WAPs2.
  assert (Fs2 : live A0 (Z_to_bv 64 s2) = None).
  { destruct (live A0 (Z_to_bv 64 s2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Fs2x | (rewrite Fs2x in XX; discriminate XX)]. }
  pose proof Lo4 as Ls2_a5.
  assert (SUB5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 s2) by (intros ->; rewrite Fs2 in Lq; discriminate Lq). rewrite (LEQ4 q NEq). exact (SUB4 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 s2 :: [Z_to_bv 64 s1; Z_to_bv 64 cstr; Z_to_bv 64 arr; Z_to_bv 64 sa])) => eq_trans (LEQ4 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL4 q (fun XX => Hq (or_intror XX)))) as LDEL5.
  assert (NE_sa_s2 : Z_to_bv 64 sa <> Z_to_bv 64 s2) by (intros EE; rewrite EE in Lsa_a4; rewrite Fs2x in Lsa_a4; discriminate Lsa_a4).
  assert (Lsa_a5 : live A5 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ4 _ NE_sa_s2); exact Lsa_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ sa s2 24 7 CK HW5 Lsa_a5 Ls2_a5 NE_sa_s2 RRsa RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_s2.
  assert (NE_arr_s2 : Z_to_bv 64 arr <> Z_to_bv 64 s2) by (intros EE; rewrite EE in Larr_a4; rewrite Fs2x in Larr_a4; discriminate Larr_a4).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ4 _ NE_arr_s2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ arr s2 400 7 CK HW5 Larr_a5 Ls2_a5 NE_arr_s2 RRarr RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_s2.
  assert (NE_cstr_s2 : Z_to_bv 64 cstr <> Z_to_bv 64 s2) by (intros EE; rewrite EE in Lcstr_a4; rewrite Fs2x in Lcstr_a4; discriminate Lcstr_a4).
  assert (Lcstr_a5 : live A5 (Z_to_bv 64 cstr) = Some 13%Z) by (rewrite (LEQ4 _ NE_cstr_s2); exact Lcstr_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ cstr s2 13 7 CK HW5 Lcstr_a5 Ls2_a5 NE_cstr_s2 RRcstr RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_cstr_s2.
  assert (NE_s1_s2 : Z_to_bv 64 s1 <> Z_to_bv 64 s2) by (intros EE; rewrite EE in Ls1_a4; rewrite Fs2x in Ls1_a4; discriminate Ls1_a4).
  assert (Ls1_a5 : live A5 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ4 _ NE_s1_s2); exact Ls1_a4).
  pose proof (exW_blk_apart_h C A5 m5 _ s1 s2 6 7 CK HW5 Ls1_a5 Ls2_a5 NE_s1_s2 RRs1 RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_s2.
  assert (PM5 : POSTM C A0 s m0 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4|]. apply (POSTM_sub C A0 A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
  replace (kR - 4 - 1)%Z with (kR - 5)%Z in RM5 by lia. rewrite MG4 in RM5. replace (bR - 4 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 5 * 2 ^ 17)%Z in RM5 by lia.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 136, 0%Z, 13%Z); (EVar 170, 0%Z, 6%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF4 4096 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 68) sa 24 CK HWs4 Lsa_a4 RRsa eq_refl (proj2 PMc4) Lsa_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 102) arr 400 CK HWs4 Larr_a4 RRarr eq_refl (proj2 PMc4) Larr_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 136) cstr 13 CK HWs4 Lcstr_a4 RRcstr eq_refl (proj2 PMc4) Lcstr_a4 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A4 A4 M4 _ M4 m5 E4 (EVar 170) s1 6 CK HWs4 Ls1_a4 RRs1 eq_refl (proj2 PMc4) Ls1_a4 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk4 kk' EQ) as HKk4_; clear EQ HKk4; rename HKk4_ into HKk4 end.
  pose proof (regs_ok_agree 172%nat E4 (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [s2; exW_canary SEGS 1410112 m5] 172%nat ltac:(vm_cast_no_check (eq_refl 172%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 172%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  try rewrite (fr_denot_agree 172%nat E4 (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 204) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 PM4 HW4 PMc4 CS4 OFF4 BS4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 SUB4 RM4 MG4 TOP4 LEQ4 Hnz4 Fs2x Lo4 LDEL4 Lsa_a4 Larr_a4 Lcstr_a4 Ls1_a4.
  repeat match goal with H : getr Rc4 _ = _ |- _ => clear H end.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn5 sr' EQ : regs_ok EE sr' RR) as HRn5_; clear EQ HRn5; rename HRn5_ into HRn5 end.
  pose proof (exW_kn_blk SEGS C A5 m5 _ (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) (EVar 204) (EVar 32) s2 7 s 4096 65536 1347584 p16_segs CK HW5 Ls2_a5 RRs2 eq_refl eq_refl eq_refl RS ALs2 ZERO_s2 WAPs2 IMGAPs2) as HKb5.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5 (EVar 68) (EVar 204) sa s2 0 24 0 7 eq_refl eq_refl RRsa RRs2 AP_sa_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5))) as HKd_sa_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5 (EVar 102) (EVar 204) arr s2 0 400 0 7 eq_refl eq_refl RRarr RRs2 AP_arr_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5))) as HKd_arr_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5 (EVar 136) (EVar 204) cstr s2 0 13 0 7 eq_refl eq_refl RRcstr RRs2 AP_cstr_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5))) as HKd_cstr_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5) _ _ (ex_kdisj_apart SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5 (EVar 170) (EVar 204) s1 s2 0 6 0 7 eq_refl eq_refl RRs1 RRs2 AP_s1_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) m5))) as HKd_s1_s2.
  pose proof (W_sok_win C A5 m5 _ (s - 4096) (Z.to_nat 4096) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [s2; exW_canary SEGS 1410112 m5]).
  pose proof (exW_kn_fixed SEGS C A5 m5 _ (ex_envL vals4 r5 [s2; exW_canary SEGS 1410112 m5]) (EVar 205) (EVar 32) (exW_canary SEGS 1410112 m5) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb5 (proj2 (Forall_app _ _ _) (conj HKd_sa_s2 (proj2 (Forall_app _ _ _) (conj HKd_arr_s2 (proj2 (Forall_app _ _ _) (conj HKd_cstr_s2 (proj2 (Forall_app _ _ _) (conj HKd_s1_s2 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  pose proof (mcs_canary_eq C A5 m5 _ CK HW5) as CEQ5.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb5 HKd_sa_s2 HKd_arr_s2 HKd_cstr_s2 HKd_s1_s2 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_s2.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A5 M5 (with_vmmaps vm5 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A5 A0 m5 _ E5 log5 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 136, cstr, 13%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW5 SUB5 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a5 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a5 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRcstr (conj Lcstr_a5 (conj Fcstr F0cstr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a5 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a5 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A5 M5 _ Rc5 (Z_to_bv 64 cstr) (Z_to_bv 64 ret) 13 sp' S CK HWs5 Q10_5 Lcstr_a5 F0cstr Q1_5
             ltac:(red; apply bv_eq; reflexivity) Q4_5 Q2_5 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A6 m6 vm6 r6 HW6 CSx5 Ldead5 LEQ5 PMc5 RTR5.
  pose proof CSx5 as CS5. clear CSx5.
  rewrite with_vmmaps_twice in HW6 |- *.
  assert (SUB6 : sub_live A0 A6).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 cstr) by (intros ->; rewrite Fcstr in Lq; discriminate Lq). rewrite (LEQ5 q NEq). exact (SUB5 q kq Lq). }
  assert (LDEL6 : forall q : word, ~ In q [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] -> live A6 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 cstr = q)) as [<-|NEq]; [rewrite Ldead5, Fcstr; reflexivity|]. rewrite (LEQ5 q (fun EE => NEq (eq_sym EE))). apply LDEL5. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lsa_a6 : live A6 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ5 _ NE_sa_cstr); exact Lsa_a5).
  assert (Larr_a6 : live A6 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ5 _ NE_arr_cstr); exact Larr_a5).
  assert (Ls1_a6 : live A6 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ5 _ (not_eq_sym NE_cstr_s1)); exact Ls1_a5).
  assert (Ls2_a6 : live A6 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ5 _ (not_eq_sym NE_cstr_s2)); exact Ls2_a5).
  assert (PM6 : POSTM C A0 s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (RTR5 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(lia) ltac:(lia)) as RM6. rewrite !Z.sub_0_r in RM6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF5 4096 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 m6 _ M5 m6 E5 (EVar 68) sa 24 CK HW6 Lsa_a6 RRsa eq_refl (proj2 PMc5) Lsa_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 m6 _ M5 m6 E5 (EVar 102) arr 400 CK HW6 Larr_a6 RRarr eq_refl (proj2 PMc5) Larr_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 m6 _ M5 m6 E5 (EVar 170) s1 6 CK HW6 Ls1_a6 RRs1 eq_refl (proj2 PMc5) Ls1_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 m6 _ M5 m6 E5 (EVar 204) s2 7 CK HW6 Ls2_a6 RRs2 eq_refl (proj2 PMc5) Ls2_a6 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [136%nat] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk5 kk' EQ) as HKk5_; clear EQ HKk5; rename HKk5_ into HKk5 end.
  pose proof (regs_ok_agree 206%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 1410112 m6] 206%nat ltac:(vm_cast_no_check (eq_refl 206%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 206%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  try rewrite (fr_denot_agree 206%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 PM5 HW5 PMc5 CS5 OFF5 BS5 Q10_5 Q1_5 Q2_5 Q4_5 SUB5 RM5 Ldead5 LEQ5 RTR5 Lcstr_a5 LDEL5 Lsa_a5 Larr_a5 Ls1_a5 Ls2_a5.
  repeat match goal with H : getr Rc5 _ = _ |- _ => clear H end.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn6 sr' EQ : regs_ok EE sr' RR) as HRn6_; clear EQ HRn6; rename HRn6_ into HRn6 end.
  pose proof (W_sok_win C A6 m6 _ (s - 4096) (Z.to_nat 4096) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m6]).
  pose proof (exW_kn_fixed SEGS C A6 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) (EVar 238) (EVar 32) (exW_canary SEGS 1410112 m6) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  pose proof (mcs_canary_eq C A6 m6 _ CK HW6) as CEQ6.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 [false] FDEF HK ST FZ.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A6 M6 (with_vmmaps vm6 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A6 A0 m6 _ E6 log6 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW6 SUB6 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a6 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a6 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a6 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 0%Z 1%nat Cb6_0.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 1%Z 1%nat Cb6_1.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 2%Z 1%nat Cb6_2.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 3%Z 1%nat Cb6_3.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 4%Z 1%nat Cb6_4.
  exW_cellB HK Hlf r0 BS6 (EVar 170) s1 5%Z 1%nat Cb6_5.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop5 fxk C A6 A0 M6 _ Rc6 s s1 6 99 49 46 56 32 (Z_to_bv 64 ret) S CK HWs6 Ls1_a6 RRs1 eq_refl eq_refl Cb6_0 Cb6_1 Cb6_2 Cb6_3 Cb6_4 Cb6_5 Q10_6 Q1_6 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r7 m7 HW7 PMc6 EQm6 H10_6 RA6.
  pose proof (mh_cs_sl _ _ RA6) as CS6.
  assert (PM7 : POSTM C A0 s m0 m7) by (eapply POSTM_trans; [exact PM6|]; eapply POSTM_trans; [exact PMs6|exact PMc6]).
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, (-4096)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (fun x _ => EQm6 x)|].
    constructor; [exact (fun x _ => EQm6 x)|].
    constructor; [exact (fun x _ => EQm6 x)|].
    constructor; [exact (fun x _ => EQm6 x)|].
    constructor; [exact (fun x _ => EQm6 x)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk6 kk' EQ) as HKk6_; clear EQ HKk6; rename HKk6_ into HKk6 end.
  pose proof (regs_ok_agree 239%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 1410112 m7] 239%nat ltac:(vm_cast_no_check (eq_refl 239%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 239%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  try rewrite (fr_denot_agree 239%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ fr (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r7 ex_r10 (ELit 5) HRn7 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10_6)) as HRx7. clear HRn7. rename HRx7 into HRn7.
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 PM6 HW6 PMc6 CS6 OFF6 BS6 Q10_6 Q1_6 Q2_6 EQm6 H10_6 RA6 Cb6_0 Cb6_1 Cb6_2 Cb6_3 Cb6_4 Cb6_5.
  repeat match goal with H : getr Rc6 _ = _ |- _ => clear H end.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn7 sr' EQ : regs_ok EE sr' RR) as HRn7_; clear EQ HRn7; rename HRn7_ into HRn7 end.
  pose proof (W_sok_win C A6 m7 _ (s - 4096) (Z.to_nat 4096) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m7]).
  pose proof (exW_kn_fixed SEGS C A6 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) (EVar 271) (EVar 32) (exW_canary SEGS 1410112 m7) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  pose proof (mcs_canary_eq C A6 m7 _ CK HW7) as CEQ7.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A6 M7 (with_vmmaps vm6 md) /\ POSTM C A0 s m7 M7).
  { subst M7. apply (exW_win_blks C A6 A0 m7 _ E7 log7 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW7 SUB6 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a6 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a6 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a6 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a6 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP7 as [HWs7 PMs7].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r11 Q11_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  pose proof (alloc_margin_small (6 * 1) ltac:(exW_cmp)) as MG7.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_7 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A6 M7 _ Rc7 6 1 (kR - 5) (bR - 5 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs7 Q10_7 Q11_7 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_7
             ltac:(red; apply bv_eq; reflexivity) Q4_7 Q2_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m8 vm7 r8 res7 HW8 Hres7 CSx7 Hnz7 Fop1x Lo7 F0op1 LEQ7 ZERO_op1 ALop1 TOP7 PMc7 RM7.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  assert (Eres7 : res7 = Z_to_bv 64 (u res7)) by (symmetry; apply zbv_self).
  pose proof (u64_range res7) as RRop1. set (op1 := u res7) in *. clearbody op1. rewrite Eres7 in Hres7, Fop1x, Lo7, F0op1, LEQ7, ZERO_op1. clear Eres7.
  change (6 * 1)%Z with 6%Z in *.
  assert (NZop1 : (1 <= op1 < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A7 m8 _ op1 6 CK HW8 Lo7 RRop1 ltac:(lia)) as (GLop11 & GLop12 & GLop13).
  pose proof (exW_blk_img_apart_h2 C A7 m8 _ op1 6 CK HW8 Lo7 RRop1 eq_refl eq_refl) as IMGAPop1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPop1.
  pose proof (exW_win_blk_apart_h C A7 m8 _ s 4096 op1 6 CK HW8 Lo7 eq_refl RRop1 GLO1) as WAPop1.
  assert (Fop1 : live A0 (Z_to_bv 64 op1) = None).
  { destruct (live A0 (Z_to_bv 64 op1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB6 _ _ EE) as XX. first [discriminate Fop1x | (rewrite Fop1x in XX; discriminate XX)]. }
  pose proof Lo7 as Lop1_a7.
  assert (SUB7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite Fop1 in Lq; discriminate Lq). rewrite (LEQ7 q NEq). exact (SUB6 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 op1 :: [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa])) => eq_trans (LEQ7 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL6 q (fun XX => Hq (or_intror XX)))) as LDEL7.
  assert (NE_sa_op1 : Z_to_bv 64 sa <> Z_to_bv 64 op1) by (intros EE; rewrite EE in Lsa_a6; rewrite Fop1x in Lsa_a6; discriminate Lsa_a6).
  assert (Lsa_a7 : live A7 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ7 _ NE_sa_op1); exact Lsa_a6).
  pose proof (exW_blk_apart_h C A7 m8 _ sa op1 24 6 CK HW8 Lsa_a7 Lop1_a7 NE_sa_op1 RRsa RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_op1.
  assert (NE_arr_op1 : Z_to_bv 64 arr <> Z_to_bv 64 op1) by (intros EE; rewrite EE in Larr_a6; rewrite Fop1x in Larr_a6; discriminate Larr_a6).
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ7 _ NE_arr_op1); exact Larr_a6).
  pose proof (exW_blk_apart_h C A7 m8 _ arr op1 400 6 CK HW8 Larr_a7 Lop1_a7 NE_arr_op1 RRarr RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_op1.
  assert (NE_s1_op1 : Z_to_bv 64 s1 <> Z_to_bv 64 op1) by (intros EE; rewrite EE in Ls1_a6; rewrite Fop1x in Ls1_a6; discriminate Ls1_a6).
  assert (Ls1_a7 : live A7 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ7 _ NE_s1_op1); exact Ls1_a6).
  pose proof (exW_blk_apart_h C A7 m8 _ s1 op1 6 6 CK HW8 Ls1_a7 Lop1_a7 NE_s1_op1 RRs1 RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_op1.
  assert (NE_s2_op1 : Z_to_bv 64 s2 <> Z_to_bv 64 op1) by (intros EE; rewrite EE in Ls2_a6; rewrite Fop1x in Ls2_a6; discriminate Ls2_a6).
  assert (Ls2_a7 : live A7 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ7 _ NE_s2_op1); exact Ls2_a6).
  pose proof (exW_blk_apart_h C A7 m8 _ s2 op1 7 6 CK HW8 Ls2_a7 Lop1_a7 NE_s2_op1 RRs2 RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s2_op1.
  assert (PM8 : POSTM C A0 s m0 m8).
  { eapply POSTM_trans; [exact PM7|]. eapply POSTM_trans; [exact PMs7|]. apply (POSTM_sub C A0 A6 _ _ _ SUB6).
    apply (POSTM_mono C A6 (s + OFF7) s); [unfold OFF7; lia | exact PMc7]. }
  replace (kR - 5 - 1)%Z with (kR - 6)%Z in RM7 by lia. rewrite MG7 in RM7. replace (bR - 5 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 6 * 2 ^ 17)%Z in RM7 by lia.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, OFF7, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF7 4096 M7 m8 E7 (EVar 32) CK (proj1 PMc7) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 M7 _ M7 m8 E7 (EVar 68) sa 24 CK HWs7 Lsa_a6 RRsa eq_refl (proj2 PMc7) Lsa_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 M7 _ M7 m8 E7 (EVar 102) arr 400 CK HWs7 Larr_a6 RRarr eq_refl (proj2 PMc7) Larr_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 M7 _ M7 m8 E7 (EVar 170) s1 6 CK HWs7 Ls1_a6 RRs1 eq_refl (proj2 PMc7) Ls1_a6 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A6 A6 M7 _ M7 m8 E7 (EVar 204) s2 7 CK HWs7 Ls2_a6 RRs2 eq_refl (proj2 PMc7) Ls2_a6 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk7 kk' EQ) as HKk7_; clear EQ HKk7; rename HKk7_ into HKk7 end.
  pose proof (regs_ok_agree 272%nat E7 (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [op1; exW_canary SEGS 1410112 m8] 272%nat ltac:(vm_cast_no_check (eq_refl 272%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8 _) by (exact (know_ok_agree SEGS 272%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  try rewrite (fr_denot_agree 272%nat E7 (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) _ fr (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (EVar 304) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 PM7 HW7 PMc7 CS7 OFF7 BS7 Q10_7 Q11_7 Q1_7 Q2_7 Q4_7 SUB6 RM6 MG7 TOP7 LEQ7 Hnz7 Fop1x Lo7 LDEL6 Lsa_a6 Larr_a6 Ls1_a6 Ls2_a6.
  repeat match goal with H : getr Rc7 _ = _ |- _ => clear H end.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn8 sr' EQ : regs_ok EE sr' RR) as HRn8_; clear EQ HRn8; rename HRn8_ into HRn8 end.
  pose proof (exW_kn_blk SEGS C A7 m8 _ (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) (EVar 304) (EVar 32) op1 6 s 4096 65536 1347584 p16_segs CK HW8 Lop1_a7 RRop1 eq_refl eq_refl eq_refl RS ALop1 ZERO_op1 WAPop1 IMGAPop1) as HKb8.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8 (EVar 68) (EVar 304) sa op1 0 24 0 6 eq_refl eq_refl RRsa RRop1 AP_sa_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8))) as HKd_sa_op1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8 (EVar 102) (EVar 304) arr op1 0 400 0 6 eq_refl eq_refl RRarr RRop1 AP_arr_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8))) as HKd_arr_op1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8 (EVar 170) (EVar 304) s1 op1 0 6 0 6 eq_refl eq_refl RRs1 RRop1 AP_s1_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8))) as HKd_s1_op1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8) _ _ (ex_kdisj_apart SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8 (EVar 204) (EVar 304) s2 op1 0 7 0 6 eq_refl eq_refl RRs2 RRop1 AP_s2_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) m8))) as HKd_s2_op1.
  pose proof (W_sok_win C A7 m8 _ (s - 4096) (Z.to_nat 4096) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 1410112 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [op1; exW_canary SEGS 1410112 m8]).
  pose proof (exW_kn_fixed SEGS C A7 m8 _ (ex_envL vals7 r8 [op1; exW_canary SEGS 1410112 m8]) (EVar 305) (EVar 32) (exW_canary SEGS 1410112 m8) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb8 (proj2 (Forall_app _ _ _) (conj HKd_sa_op1 (proj2 (Forall_app _ _ _) (conj HKd_arr_op1 (proj2 (Forall_app _ _ _) (conj HKd_s1_op1 (proj2 (Forall_app _ _ _) (conj HKd_s2_op1 (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  pose proof (mcs_canary_eq C A7 m8 _ CK HW8) as CEQ8.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb8 HKd_sa_op1 HKd_arr_op1 HKd_s1_op1 HKd_s2_op1 HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_op1.
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A7 M8 (with_vmmaps vm7 md) /\ POSTM C A0 s m8 M8).
  { subst M8. apply (exW_win_blks C A7 A0 m8 _ E8 log8 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 304, op1, 6%Z)] CK HW8 SUB7 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a7 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a7 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a7 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a7 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP8 as [HWs8 PMs8].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BS8 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 0%Z 1%nat Cb8_0.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 1%Z 1%nat Cb8_1.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 2%Z 1%nat Cb8_2.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 3%Z 1%nat Cb8_3.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 4%Z 1%nat Cb8_4.
  exW_cellB HK Hlf r0 BS8 (EVar 170) s1 5%Z 1%nat Cb8_5.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop5 fxk C A7 A0 M8 _ Rc8 s s1 6 99 49 46 56 32 (Z_to_bv 64 ret) S CK HWs8 Ls1_a7 RRs1 eq_refl eq_refl Cb8_0 Cb8_1 Cb8_2 Cb8_3 Cb8_4 Cb8_5 Q10_8 Q1_8 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r9 m9 HW9 PMc8 EQm8 H10_8 RA8.
  pose proof (mh_cs_sl _ _ RA8) as CS8.
  assert (PM9 : POSTM C A0 s m0 m9) by (eapply POSTM_trans; [exact PM8|]; eapply POSTM_trans; [exact PMs8|exact PMc8]).
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, (-4096)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z); (EVar 304, 0%Z, 6%Z)]).
  {
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor; [exact (fun x _ => EQm8 x)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk8 kk' EQ) as HKk8_; clear EQ HKk8; rename HKk8_ into HKk8 end.
  pose proof (regs_ok_agree 306%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [exW_canary SEGS 1410112 m9] 306%nat ltac:(vm_cast_no_check (eq_refl 306%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) m9 _) by (exact (know_ok_agree SEGS 306%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  try rewrite (fr_denot_agree 306%nat E8 (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) _ fr (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r9 ex_r10 (ELit 5) HRn9 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10_8)) as HRx9. clear HRn9. rename HRx9 into HRn9.
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 PM8 HW8 PMc8 CS8 OFF8 BS8 Q10_8 Q1_8 Q2_8 EQm8 H10_8 RA8 Cb8_0 Cb8_1 Cb8_2 Cb8_3 Cb8_4 Cb8_5.
  repeat match goal with H : getr Rc8 _ = _ |- _ => clear H end.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn9 sr' EQ : regs_ok EE sr' RR) as HRn9_; clear EQ HRn9; rename HRn9_ into HRn9 end.
  pose proof (W_sok_win C A7 m9 _ (s - 4096) (Z.to_nat 4096) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 1410112 m9 (canary_any m9)) as CANOK9.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m9]).
  pose proof (exW_kn_fixed SEGS C A7 m9 _ (ex_envL vals8 r9 [exW_canary SEGS 1410112 m9]) (EVar 338) (EVar 32) (exW_canary SEGS 1410112 m9) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  pose proof (mcs_canary_eq C A7 m9 _ CK HW9) as CEQ9.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf9 HKa9 SOK9 CANOK9.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A7 M9 (with_vmmaps vm7 md) /\ POSTM C A0 s m9 M9).
  { subst M9. apply (exW_win_blks C A7 A0 m9 _ E9 log9 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 304, op1, 6%Z)] CK HW9 SUB7 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a7 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a7 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a7 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a7 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP9 as [HWs9 PMs9].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  pose (BS9 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r11 Q11_9. exW_regfactB BS9 HR ex_r12 Q12_9. exW_regfactB BS9 HR ex_r1 Q1_9. exW_regfactB BS9 HR ex_r2 Q2_9.
  lazymatch type of Q2_9 with _ = Z_to_bv 64 (s + ?off) => pose (OFF9 := off) end.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (mcs_memset_hop (fx := fxk) C A7 A0 M9 _ Rc9 s (s + -1016) 232 (Z_to_bv 64 ret) S CK HWs9 SUB7 Hhi ltac:(lia) ltac:(lia) ltac:(lia) Q1_9 ltac:(red; apply bv_eq; reflexivity) Q10_9 Q11_9 Q12_9) end end.
  intros r10 m10 HW10 PMc9 H10_9 RA9 OUT9 ZR9.
  pose proof (mh_cs_ms _ _ RA9) as CS9.
  assert (PM10 : POSTM C A0 s m0 m10) by (eapply POSTM_trans; [exact PM9|]; eapply POSTM_trans; [exact PMs9|exact PMc9]).
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-4096)%Z, (-1016)%Z); (EVar 32, (-784)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z); (EVar 304, 0%Z, 6%Z)]).
  {
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 32) s (-4096) (-1016) (s + -1016) (s + -1016 + 232) OUT9 eq_refl RS ltac:(lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 32) s (-784) 0 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RS ltac:(lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 68) sa 0 24 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RRsa ltac:(unfold ex_apart in WAPsa; lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 102) arr 0 400 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RRarr ltac:(unfold ex_apart in WAParr; lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 170) s1 0 6 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RRs1 ltac:(unfold ex_apart in WAPs1; lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 204) s2 0 7 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RRs2 ltac:(unfold ex_apart in WAPs2; lia))|].
    constructor; [exact (exW_kept_out E9 M9 m10 (EVar 304) op1 0 6 (s + -1016) (s + -1016 + 232) OUT9 eq_refl RRop1 ltac:(unfold ex_apart in WAPop1; lia))|].
    constructor. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk9 kk' EQ) as HKk9_; clear EQ HKk9; rename HKk9_ into HKk9 end.
  pose proof (regs_ok_agree 339%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 1410112 m10] 339%nat ltac:(vm_cast_no_check (eq_refl 339%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) m10 _) by (exact (know_ok_agree SEGS 339%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  try rewrite (fr_denot_agree 339%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ fr (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r10 ex_r10 (EAlu ALU_ADD (EVar 32) (ELit (-1016))) HRn10 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact (eq_trans H10_9 (eq_sym (ex_ptr_val s (-1016)))))) as HRx10. clear HRn10. rename HRx10 into HRn10.
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 PM9 HW9 PMc9 CS9 OFF9 BS9 Q10_9 Q11_9 Q12_9 Q1_9 Q2_9 RA9 OUT9.
  repeat match goal with H : getr Rc9 _ = _ |- _ => clear H end.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn10 sr' EQ : regs_ok EE sr' RR) as HRn10_; clear EQ HRn10; rename HRn10_ into HRn10 end.
  pose proof (mcs_kzero_win SEGS (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) m10 (EVar 32) s (-1016) 232 eq_refl RS ltac:(lia) eq_refl ltac:(lia) ZR9) as HKz10.
  pose proof (W_sok_win C A7 m10 _ (s - 4096) (Z.to_nat 4096) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 1410112 m10 (canary_any m10)) as CANOK10.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m10]).
  pose proof (exW_kn_fixed SEGS C A7 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) (EVar 371) (EVar 32) (exW_canary SEGS 1410112 m10) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKz10 (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  pose proof (mcs_canary_eq C A7 m10 _ CK HW10) as CEQ10.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKz10 HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  clear ZR9.
  mh_drive 2000%nat 6000%nat STOPS2 [false; false; false; false; false; false; false; true; false; false] FDEF HK ST FZ.
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A7 M10 (with_vmmaps vm7 md) /\ POSTM C A0 s m10 M10).
  { subst M10. apply (exW_win_blks C A7 A0 m10 _ E10 log10 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 304, op1, 6%Z)] CK HW10 SUB7 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a7 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a7 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a7 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a7 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a7 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP10 as [HWs10 PMs10].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  pose (BS10 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r1 Q1_10. exW_regfactB BS10 HR ex_r2 Q2_10. exW_regfactB BS10 HR ex_r4 Q4_10.
  lazymatch type of Q2_10 with _ = Z_to_bv 64 (s + ?off) => pose (OFF10 := off) end.
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_10 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A7 M10 _ Rc10 (Z_to_bv 64 op1) (Z_to_bv 64 ret) 6 sp' S CK HWs10 Q10_10 Lop1_a7 F0op1 Q1_10
             ltac:(red; apply bv_eq; reflexivity) Q4_10 Q2_10 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A8 m11 vm8 r11 HW11 CSx10 Ldead10 LEQ10 PMc10 RTR10.
  pose proof CSx10 as CS10. clear CSx10.
  rewrite with_vmmaps_twice in HW11 |- *.
  assert (SUB8 : sub_live A0 A8).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite Fop1 in Lq; discriminate Lq). rewrite (LEQ10 q NEq). exact (SUB7 q kq Lq). }
  assert (LDEL8 : forall q : word, ~ In q [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] -> live A8 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 op1 = q)) as [<-|NEq]; [rewrite Ldead10, Fop1; reflexivity|]. rewrite (LEQ10 q (fun EE => NEq (eq_sym EE))). apply LDEL7. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lsa_a8 : live A8 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ10 _ NE_sa_op1); exact Lsa_a7).
  assert (Larr_a8 : live A8 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ10 _ NE_arr_op1); exact Larr_a7).
  assert (Ls1_a8 : live A8 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ10 _ NE_s1_op1); exact Ls1_a7).
  assert (Ls2_a8 : live A8 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ10 _ NE_s2_op1); exact Ls2_a7).
  assert (PM11 : POSTM C A0 s m0 m11).
  { eapply POSTM_trans; [exact PM10|]. eapply POSTM_trans; [exact PMs10|]. apply (POSTM_sub C A0 A8 _ _ _ SUB8).
    apply (POSTM_mono C A8 (s + OFF10) s); [unfold OFF10; lia | exact PMc10]. }
  pose proof (RTR10 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(lia) ltac:(lia)) as RM8. rewrite !Z.sub_0_r in RM8.
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, OFF10, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF10 4096 M10 m11 E10 (EVar 32) CK (proj1 PMc10) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 m11 _ M10 m11 E10 (EVar 68) sa 24 CK HW11 Lsa_a8 RRsa eq_refl (proj2 PMc10) Lsa_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 m11 _ M10 m11 E10 (EVar 102) arr 400 CK HW11 Larr_a8 RRarr eq_refl (proj2 PMc10) Larr_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 m11 _ M10 m11 E10 (EVar 170) s1 6 CK HW11 Ls1_a8 RRs1 eq_refl (proj2 PMc10) Ls1_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 m11 _ M10 m11 E10 (EVar 204) s2 7 CK HW11 Ls2_a8 RRs2 eq_refl (proj2 PMc10) Ls2_a8 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [304%nat] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk10 kk' EQ) as HKk10_; clear EQ HKk10; rename HKk10_ into HKk10 end.
  pose proof (regs_ok_agree 372%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [exW_canary SEGS 1410112 m11] 372%nat ltac:(vm_cast_no_check (eq_refl 372%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) m11 _) by (exact (know_ok_agree SEGS 372%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  try rewrite (fr_denot_agree 372%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) _ fr (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 PM10 HW10 PMc10 CS10 OFF10 BS10 Q10_10 Q1_10 Q2_10 Q4_10 SUB7 RM7 Ldead10 LEQ10 RTR10 Lop1_a7 LDEL7 Lsa_a7 Larr_a7 Ls1_a7 Ls2_a7.
  repeat match goal with H : getr Rc10 _ = _ |- _ => clear H end.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn11 sr' EQ : regs_ok EE sr' RR) as HRn11_; clear EQ HRn11; rename HRn11_ into HRn11 end.
  pose proof (W_sok_win C A8 m11 _ (s - 4096) (Z.to_nat 4096) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 1410112 m11 (canary_any m11)) as CANOK11.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m11]).
  pose proof (exW_kn_fixed SEGS C A8 m11 _ (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) (EVar 404) (EVar 32) (exW_canary SEGS 1410112 m11) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW11 eq_refl (proj1 CANOK11) (proj2 CANOK11) eq_refl eq_refl eq_refl SOK11 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf11.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf11 HKa11)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn11 into HR.
  pose proof (mcs_canary_eq C A8 m11 _ CK HW11) as CEQ11.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN11 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf11 HKa11 SOK11 CANOK11.
  repeat match goal with H : getr r11 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 [false] FDEF HK ST FZ.
  exb_exit ST Rc11 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E11 := EEx) in HR, Hlf, HK, Hms |- *; set (log11 := LLx) in Hms, Hlf; set (M11 := mem_denot E11 m11 log11) in Hms end.
  assert (WP11 : W C A8 M11 (with_vmmaps vm8 md) /\ POSTM C A0 s m11 M11).
  { subst M11. apply (exW_win_blks C A8 A0 m11 _ E11 log11 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW11 SUB8 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a8 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a8 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a8 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a8 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP11 as [HWs11 PMs11].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  pose (BS11 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 0%Z 1%nat Cb11_0.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 1%Z 1%nat Cb11_1.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 2%Z 1%nat Cb11_2.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 3%Z 1%nat Cb11_3.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 4%Z 1%nat Cb11_4.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 5%Z 1%nat Cb11_5.
  exW_cellB HK Hlf r0 BS11 (EVar 204) s2 6%Z 1%nat Cb11_6.
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop6 fxk C A8 A0 M11 _ Rc11 s s2 7 32 99 51 48 46 49 (Z_to_bv 64 ret) S CK HWs11 Ls2_a8 RRs2 eq_refl eq_refl Cb11_0 Cb11_1 Cb11_2 Cb11_3 Cb11_4 Cb11_5 Cb11_6 Q10_11 Q1_11 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r12 m12 HW12 PMc11 EQm11 H10_11 RA11.
  pose proof (mh_cs_sl _ _ RA11) as CS11.
  assert (PM12 : POSTM C A0 s m0 m12) by (eapply POSTM_trans; [exact PM11|]; eapply POSTM_trans; [exact PMs11|exact PMc11]).
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, (-4096)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (fun x _ => EQm11 x)|].
    constructor; [exact (fun x _ => EQm11 x)|].
    constructor; [exact (fun x _ => EQm11 x)|].
    constructor; [exact (fun x _ => EQm11 x)|].
    constructor; [exact (fun x _ => EQm11 x)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk11 kk' EQ) as HKk11_; clear EQ HKk11; rename HKk11_ into HKk11 end.
  pose proof (regs_ok_agree 405%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [exW_canary SEGS 1410112 m12] 405%nat ltac:(vm_cast_no_check (eq_refl 405%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) m12 _) by (exact (know_ok_agree SEGS 405%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  try rewrite (fr_denot_agree 405%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) _ fr (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r12 ex_r10 (ELit 6) HRn12 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10_11)) as HRx12. clear HRn12. rename HRx12 into HRn12.
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 PM11 HW11 PMc11 CS11 OFF11 BS11 Q10_11 Q1_11 Q2_11 EQm11 H10_11 RA11 Cb11_0 Cb11_1 Cb11_2 Cb11_3 Cb11_4 Cb11_5 Cb11_6.
  repeat match goal with H : getr Rc11 _ = _ |- _ => clear H end.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn12 sr' EQ : regs_ok EE sr' RR) as HRn12_; clear EQ HRn12; rename HRn12_ into HRn12 end.
  pose proof (W_sok_win C A8 m12 _ (s - 4096) (Z.to_nat 4096) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 1410112 m12 (canary_any m12)) as CANOK12.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m12]).
  pose proof (exW_kn_fixed SEGS C A8 m12 _ (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) (EVar 437) (EVar 32) (exW_canary SEGS 1410112 m12) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW12 eq_refl (proj1 CANOK12) (proj2 CANOK12) eq_refl eq_refl eq_refl SOK12 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf12.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf12 HKa12)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn12 into HR.
  pose proof (mcs_canary_eq C A8 m12 _ CK HW12) as CEQ12.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN12 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf12 HKa12 SOK12 CANOK12.
  repeat match goal with H : getr r12 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc12 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E12 := EEx) in HR, Hlf, HK, Hms |- *; set (log12 := LLx) in Hms, Hlf; set (M12 := mem_denot E12 m12 log12) in Hms end.
  assert (WP12 : W C A8 M12 (with_vmmaps vm8 md) /\ POSTM C A0 s m12 M12).
  { subst M12. apply (exW_win_blks C A8 A0 m12 _ E12 log12 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW12 SUB8 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a8 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a8 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a8 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a8 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP12 as [HWs12 PMs12].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  pose (BS12 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r11 Q11_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  pose proof (alloc_margin_small (7 * 1) ltac:(exW_cmp)) as MG12.
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_calloc16_sure (fx := fxk) C A8 M12 _ Rc12 7 1 (kR - 6) (bR - 6 * 2 ^ 17) (Z_to_bv 64 ret) sp' S CK HWs12 Q10_12 Q11_12 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(lia) ltac:(lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A9 m13 vm9 r13 res12 HW13 Hres12 CSx12 Hnz12 Fop2x Lo12 F0op2 LEQ12 ZERO_op2 ALop2 TOP12 PMc12 RM9.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (Eres12 : res12 = Z_to_bv 64 (u res12)) by (symmetry; apply zbv_self).
  pose proof (u64_range res12) as RRop2. set (op2 := u res12) in *. clearbody op2. rewrite Eres12 in Hres12, Fop2x, Lo12, F0op2, LEQ12, ZERO_op2. clear Eres12.
  change (7 * 1)%Z with 7%Z in *.
  assert (NZop2 : (1 <= op2 < 2 ^ 64)%Z) by lia.
  destruct (exW_blk_rng C A9 m13 _ op2 7 CK HW13 Lo12 RRop2 ltac:(lia)) as (GLop21 & GLop22 & GLop23).
  pose proof (exW_blk_img_apart_h2 C A9 m13 _ op2 7 CK HW13 Lo12 RRop2 eq_refl eq_refl) as IMGAPop2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPop2.
  pose proof (exW_win_blk_apart_h C A9 m13 _ s 4096 op2 7 CK HW13 Lo12 eq_refl RRop2 GLO1) as WAPop2.
  assert (Fop2 : live A0 (Z_to_bv 64 op2) = None).
  { destruct (live A0 (Z_to_bv 64 op2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB8 _ _ EE) as XX. first [discriminate Fop2x | (rewrite Fop2x in XX; discriminate XX)]. }
  pose proof Lo12 as Lop2_a9.
  assert (SUB9 : sub_live A0 A9).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite Fop2 in Lq; discriminate Lq). rewrite (LEQ12 q NEq). exact (SUB8 q kq Lq). }
  pose proof (fun (q : word) (Hq : ~ In q (Z_to_bv 64 op2 :: [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa])) => eq_trans (LEQ12 q (fun EE => Hq (or_introl (eq_sym EE)))) (LDEL8 q (fun XX => Hq (or_intror XX)))) as LDEL9.
  assert (NE_sa_op2 : Z_to_bv 64 sa <> Z_to_bv 64 op2) by (intros EE; rewrite EE in Lsa_a8; rewrite Fop2x in Lsa_a8; discriminate Lsa_a8).
  assert (Lsa_a9 : live A9 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ12 _ NE_sa_op2); exact Lsa_a8).
  pose proof (exW_blk_apart_h C A9 m13 _ sa op2 24 7 CK HW13 Lsa_a9 Lop2_a9 NE_sa_op2 RRsa RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_op2.
  assert (NE_arr_op2 : Z_to_bv 64 arr <> Z_to_bv 64 op2) by (intros EE; rewrite EE in Larr_a8; rewrite Fop2x in Larr_a8; discriminate Larr_a8).
  assert (Larr_a9 : live A9 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ12 _ NE_arr_op2); exact Larr_a8).
  pose proof (exW_blk_apart_h C A9 m13 _ arr op2 400 7 CK HW13 Larr_a9 Lop2_a9 NE_arr_op2 RRarr RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_op2.
  assert (NE_s1_op2 : Z_to_bv 64 s1 <> Z_to_bv 64 op2) by (intros EE; rewrite EE in Ls1_a8; rewrite Fop2x in Ls1_a8; discriminate Ls1_a8).
  assert (Ls1_a9 : live A9 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ12 _ NE_s1_op2); exact Ls1_a8).
  pose proof (exW_blk_apart_h C A9 m13 _ s1 op2 6 7 CK HW13 Ls1_a9 Lop2_a9 NE_s1_op2 RRs1 RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_op2.
  assert (NE_s2_op2 : Z_to_bv 64 s2 <> Z_to_bv 64 op2) by (intros EE; rewrite EE in Ls2_a8; rewrite Fop2x in Ls2_a8; discriminate Ls2_a8).
  assert (Ls2_a9 : live A9 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ12 _ NE_s2_op2); exact Ls2_a8).
  pose proof (exW_blk_apart_h C A9 m13 _ s2 op2 7 7 CK HW13 Ls2_a9 Lop2_a9 NE_s2_op2 RRs2 RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s2_op2.
  assert (PM13 : POSTM C A0 s m0 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C A0 A8 _ _ _ SUB8).
    apply (POSTM_mono C A8 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  replace (kR - 6 - 1)%Z with (kR - 7)%Z in RM9 by lia. rewrite MG12 in RM9. replace (bR - 6 * 2 ^ 17 - 2 ^ 17)%Z with (bR - 7 * 2 ^ 17)%Z in RM9 by lia.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF12 4096 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 M12 _ M12 m13 E12 (EVar 68) sa 24 CK HWs12 Lsa_a8 RRsa eq_refl (proj2 PMc12) Lsa_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 M12 _ M12 m13 E12 (EVar 102) arr 400 CK HWs12 Larr_a8 RRarr eq_refl (proj2 PMc12) Larr_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 M12 _ M12 m13 E12 (EVar 170) s1 6 CK HWs12 Ls1_a8 RRs1 eq_refl (proj2 PMc12) Ls1_a8 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A8 A8 M12 _ M12 m13 E12 (EVar 204) s2 7 CK HWs12 Ls2_a8 RRs2 eq_refl (proj2 PMc12) Ls2_a8 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk12 kk' EQ) as HKk12_; clear EQ HKk12; rename HKk12_ into HKk12 end.
  pose proof (regs_ok_agree 438%nat E12 (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [op2; exW_canary SEGS 1410112 m13] 438%nat ltac:(vm_cast_no_check (eq_refl 438%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13 _) by (exact (know_ok_agree SEGS 438%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  try rewrite (fr_denot_agree 438%nat E12 (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) _ fr (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r13 ex_r10 (EVar 470) HRn13 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres12)) as HRx13. clear HRn13. rename HRx13 into HRn13.
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 PM12 HW12 PMc12 CS12 OFF12 BS12 Q10_12 Q11_12 Q1_12 Q2_12 Q4_12 SUB8 RM8 MG12 TOP12 LEQ12 Hnz12 Fop2x Lo12 LDEL8 Lsa_a8 Larr_a8 Ls1_a8 Ls2_a8.
  repeat match goal with H : getr Rc12 _ = _ |- _ => clear H end.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn13 sr' EQ : regs_ok EE sr' RR) as HRn13_; clear EQ HRn13; rename HRn13_ into HRn13 end.
  pose proof (exW_kn_blk SEGS C A9 m13 _ (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) (EVar 470) (EVar 32) op2 7 s 4096 65536 1347584 p16_segs CK HW13 Lop2_a9 RRop2 eq_refl eq_refl eq_refl RS ALop2 ZERO_op2 WAPop2 IMGAPop2) as HKb13.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13 (EVar 68) (EVar 470) sa op2 0 24 0 7 eq_refl eq_refl RRsa RRop2 AP_sa_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13))) as HKd_sa_op2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13 (EVar 102) (EVar 470) arr op2 0 400 0 7 eq_refl eq_refl RRarr RRop2 AP_arr_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13))) as HKd_arr_op2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13 (EVar 170) (EVar 470) s1 op2 0 6 0 7 eq_refl eq_refl RRs1 RRop2 AP_s1_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13))) as HKd_s1_op2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13) _ _ (ex_kdisj_apart SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13 (EVar 204) (EVar 470) s2 op2 0 7 0 7 eq_refl eq_refl RRs2 RRop2 AP_s2_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) m13))) as HKd_s2_op2.
  pose proof (W_sok_win C A9 m13 _ (s - 4096) (Z.to_nat 4096) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 1410112 m13 (canary_any m13)) as CANOK13.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [op2; exW_canary SEGS 1410112 m13]).
  pose proof (exW_kn_fixed SEGS C A9 m13 _ (ex_envL vals12 r13 [op2; exW_canary SEGS 1410112 m13]) (EVar 471) (EVar 32) (exW_canary SEGS 1410112 m13) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb13 (proj2 (Forall_app _ _ _) (conj HKd_sa_op2 (proj2 (Forall_app _ _ _) (conj HKd_arr_op2 (proj2 (Forall_app _ _ _) (conj HKd_s1_op2 (proj2 (Forall_app _ _ _) (conj HKd_s2_op2 (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  pose proof (mcs_canary_eq C A9 m13 _ CK HW13) as CEQ13.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKb13 HKd_sa_op2 HKd_arr_op2 HKd_s1_op2 HKd_s2_op2 HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  clear ZERO_op2.
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A9 M13 (with_vmmaps vm9 md) /\ POSTM C A0 s m13 M13).
  { subst M13. apply (exW_win_blks C A9 A0 m13 _ E13 log13 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 470, op2, 7%Z)] CK HW13 SUB9 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a9 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a9 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a9 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a9 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a9 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP13 as [HWs13 PMs13].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  pose (BS13 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1); (470%nat, op2)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 0%Z 1%nat Cb13_0.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 1%Z 1%nat Cb13_1.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 2%Z 1%nat Cb13_2.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 3%Z 1%nat Cb13_3.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 4%Z 1%nat Cb13_4.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 5%Z 1%nat Cb13_5.
  exW_cellB HK Hlf r0 BS13 (EVar 204) s2 6%Z 1%nat Cb13_6.
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop6 fxk C A9 A0 M13 _ Rc13 s s2 7 32 99 51 48 46 49 (Z_to_bv 64 ret) S CK HWs13 Ls2_a9 RRs2 eq_refl eq_refl Cb13_0 Cb13_1 Cb13_2 Cb13_3 Cb13_4 Cb13_5 Cb13_6 Q10_13 Q1_13 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r14 m14 HW14 PMc13 EQm13 H10_13 RA13.
  pose proof (mh_cs_sl _ _ RA13) as CS13.
  assert (PM14 : POSTM C A0 s m0 m14) by (eapply POSTM_trans; [exact PM13|]; eapply POSTM_trans; [exact PMs13|exact PMc13]).
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, (-4096)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z); (EVar 470, 0%Z, 7%Z)]).
  {
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor; [exact (fun x _ => EQm13 x)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk13 kk' EQ) as HKk13_; clear EQ HKk13; rename HKk13_ into HKk13 end.
  pose proof (regs_ok_agree 472%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [exW_canary SEGS 1410112 m14] 472%nat ltac:(vm_cast_no_check (eq_refl 472%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) m14 _) by (exact (know_ok_agree SEGS 472%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  try rewrite (fr_denot_agree 472%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) _ fr (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r14 ex_r10 (ELit 6) HRn14 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact H10_13)) as HRx14. clear HRn14. rename HRx14 into HRn14.
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 PM13 HW13 PMc13 CS13 OFF13 BS13 Q10_13 Q1_13 Q2_13 EQm13 H10_13 RA13 Cb13_0 Cb13_1 Cb13_2 Cb13_3 Cb13_4 Cb13_5 Cb13_6.
  repeat match goal with H : getr Rc13 _ = _ |- _ => clear H end.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn14 sr' EQ : regs_ok EE sr' RR) as HRn14_; clear EQ HRn14; rename HRn14_ into HRn14 end.
  pose proof (W_sok_win C A9 m14 _ (s - 4096) (Z.to_nat 4096) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 1410112 m14 (canary_any m14)) as CANOK14.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m14]).
  pose proof (exW_kn_fixed SEGS C A9 m14 _ (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) (EVar 504) (EVar 32) (exW_canary SEGS 1410112 m14) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  pose proof (mcs_canary_eq C A9 m14 _ CK HW14) as CEQ14.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A9 M14 (with_vmmaps vm9 md) /\ POSTM C A0 s m14 M14).
  { subst M14. apply (exW_win_blks C A9 A0 m14 _ E14 log14 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 470, op2, 7%Z)] CK HW14 SUB9 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a9 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a9 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a9 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a9 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a9 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP14 as [HWs14 PMs14].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose (BS14 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1); (470%nat, op2)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r11 Q11_14. exW_regfactB BS14 HR ex_r12 Q12_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (mcs_memset_hop (fx := fxk) C A9 A0 M14 _ Rc14 s (s + -1016) 232 (Z_to_bv 64 ret) S CK HWs14 SUB9 Hhi ltac:(lia) ltac:(lia) ltac:(lia) Q1_14 ltac:(red; apply bv_eq; reflexivity) Q10_14 Q11_14 Q12_14) end end.
  intros r15 m15 HW15 PMc14 H10_14 RA14 OUT14 ZR14.
  pose proof (mh_cs_ms _ _ RA14) as CS14.
  assert (PM15 : POSTM C A0 s m0 m15) by (eapply POSTM_trans; [exact PM14|]; eapply POSTM_trans; [exact PMs14|exact PMc14]).
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, (-4096)%Z, (-1016)%Z); (EVar 32, (-784)%Z, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z); (EVar 470, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 32) s (-4096) (-1016) (s + -1016) (s + -1016 + 232) OUT14 eq_refl RS ltac:(lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 32) s (-784) 0 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RS ltac:(lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 68) sa 0 24 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RRsa ltac:(unfold ex_apart in WAPsa; lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 102) arr 0 400 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RRarr ltac:(unfold ex_apart in WAParr; lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 170) s1 0 6 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RRs1 ltac:(unfold ex_apart in WAPs1; lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 204) s2 0 7 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RRs2 ltac:(unfold ex_apart in WAPs2; lia))|].
    constructor; [exact (exW_kept_out E14 M14 m15 (EVar 470) op2 0 7 (s + -1016) (s + -1016 + 232) OUT14 eq_refl RRop2 ltac:(unfold ex_apart in WAPop2; lia))|].
    constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk14 kk' EQ) as HKk14_; clear EQ HKk14; rename HKk14_ into HKk14 end.
  pose proof (regs_ok_agree 505%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [exW_canary SEGS 1410112 m15] 505%nat ltac:(vm_cast_no_check (eq_refl 505%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) m15 _) by (exact (know_ok_agree SEGS 505%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  try rewrite (fr_denot_agree 505%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) _ fr (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r15 ex_r10 (EAlu ALU_ADD (EVar 32) (ELit (-1016))) HRn15 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact (eq_trans H10_14 (eq_sym (ex_ptr_val s (-1016)))))) as HRx15. clear HRn15. rename HRx15 into HRn15.
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 PM14 HW14 PMc14 CS14 OFF14 BS14 Q10_14 Q11_14 Q12_14 Q1_14 Q2_14 RA14 OUT14.
  repeat match goal with H : getr Rc14 _ = _ |- _ => clear H end.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn15 sr' EQ : regs_ok EE sr' RR) as HRn15_; clear EQ HRn15; rename HRn15_ into HRn15 end.
  pose proof (mcs_kzero_win SEGS (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) m15 (EVar 32) s (-1016) 232 eq_refl RS ltac:(lia) eq_refl ltac:(lia) ZR14) as HKz15.
  pose proof (W_sok_win C A9 m15 _ (s - 4096) (Z.to_nat 4096) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 1410112 m15 (canary_any m15)) as CANOK15.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m15]).
  pose proof (exW_kn_fixed SEGS C A9 m15 _ (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) (EVar 537) (EVar 32) (exW_canary SEGS 1410112 m15) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKz15 (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  pose proof (mcs_canary_eq C A9 m15 _ CK HW15) as CEQ15.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKz15 HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  clear ZR14.
  mh_drive 2000%nat 6000%nat STOPS2 [false; false; false; false; false; false; false; false; false; false; false; false] FDEF HK ST FZ.
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A9 M15 (with_vmmaps vm9 md) /\ POSTM C A0 s m15 M15).
  { subst M15. apply (exW_win_blks C A9 A0 m15 _ E15 log15 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z); (EVar 470, op2, 7%Z)] CK HW15 SUB9 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a9 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a9 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a9 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a9 (conj Fs2 F0s2))))|].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a9 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP15 as [HWs15 PMs15].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose (BS15 := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1); (470%nat, op2)]).
  exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r1 Q1_15. exW_regfactB BS15 HR ex_r2 Q2_15. exW_regfactB BS15 HR ex_r4 Q4_15.
  lazymatch type of Q2_15 with _ = Z_to_bv 64 (s + ?off) => pose (OFF15 := off) end.
  lazymatch type of Q1_15 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_15 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A9 M15 _ Rc15 (Z_to_bv 64 op2) (Z_to_bv 64 ret) 7 sp' S CK HWs15 Q10_15 Lop2_a9 F0op2 Q1_15
             ltac:(red; apply bv_eq; reflexivity) Q4_15 Q2_15 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A10 m16 vm10 r16 HW16 CSx15 Ldead15 LEQ15 PMc15 RTR15.
  pose proof CSx15 as CS15. clear CSx15.
  rewrite with_vmmaps_twice in HW16 |- *.
  assert (SUB10 : sub_live A0 A10).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite Fop2 in Lq; discriminate Lq). rewrite (LEQ15 q NEq). exact (SUB9 q kq Lq). }
  assert (LDEL10 : forall q : word, ~ In q [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] -> live A10 q = live A0 q).
  { intros q Hq. destruct (decide (Z_to_bv 64 op2 = q)) as [<-|NEq]; [rewrite Ldead15, Fop2; reflexivity|]. rewrite (LEQ15 q (fun EE => NEq (eq_sym EE))). apply LDEL9. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (Lsa_a10 : live A10 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ15 _ NE_sa_op2); exact Lsa_a9).
  assert (Larr_a10 : live A10 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ15 _ NE_arr_op2); exact Larr_a9).
  assert (Ls1_a10 : live A10 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ15 _ NE_s1_op2); exact Ls1_a9).
  assert (Ls2_a10 : live A10 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ15 _ NE_s2_op2); exact Ls2_a9).
  assert (PM16 : POSTM C A0 s m0 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15|]. apply (POSTM_sub C A0 A10 _ _ _ SUB10).
    apply (POSTM_mono C A10 (s + OFF15) s); [unfold OFF15; lia | exact PMc15]. }
  pose proof (RTR15 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(lia) ltac:(lia)) as RM10. rewrite !Z.sub_0_r in RM10.
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, OFF15, 0%Z); (EVar 68, 0%Z, 24%Z); (EVar 102, 0%Z, 400%Z); (EVar 170, 0%Z, 6%Z); (EVar 204, 0%Z, 7%Z)]).
  {
    constructor; [exact (exW_kept_stack2 C s OFF15 4096 M15 m16 E15 (EVar 32) CK (proj1 PMc15) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A10 A10 m16 _ M15 m16 E15 (EVar 68) sa 24 CK HW16 Lsa_a10 RRsa eq_refl (proj2 PMc15) Lsa_a10 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A10 A10 m16 _ M15 m16 E15 (EVar 102) arr 400 CK HW16 Larr_a10 RRarr eq_refl (proj2 PMc15) Larr_a10 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A10 A10 m16 _ M15 m16 E15 (EVar 170) s1 6 CK HW16 Ls1_a10 RRs1 eq_refl (proj2 PMc15) Ls1_a10 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A10 A10 m16 _ M15 m16 E15 (EVar 204) s2 7 CK HW16 Ls2_a10 RRs2 eq_refl (proj2 PMc15) Ls2_a10 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [470%nat] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok ?sg ?ee ?mm ?kk => let kk' := eval vm_compute in kk in let EQ := fresh "EQ" in assert (EQ : kk = kk') by (vm_cast_no_check (eq_refl kk')); pose proof (@eq_rect _ kk (know_ok sg ee mm) HKk15 kk' EQ) as HKk15_; clear EQ HKk15; rename HKk15_ into HKk15 end.
  pose proof (regs_ok_agree 538%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_call _ _ _ _ _ HRa15 (ex_regs_ok_junk vals15 r16 [exW_canary SEGS 1410112 m16] 538%nat ltac:(vm_cast_no_check (eq_refl 538%nat))) CS15) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) m16 _) by (exact (know_ok_agree SEGS 538%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  try rewrite (fr_denot_agree 538%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) _ fr (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 PM15 HW15 PMc15 CS15 OFF15 BS15 Q10_15 Q1_15 Q2_15 Q4_15 SUB9 RM9 Ldead15 LEQ15 RTR15 Lop2_a9 LDEL9 Lsa_a9 Larr_a9 Ls1_a9 Ls2_a9.
  repeat match goal with H : getr Rc15 _ = _ |- _ => clear H end.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in let EQ := fresh "EQ" in assert (EQ : sr = sr') by (vm_cast_no_check (eq_refl sr')); pose proof (@eq_rect _ sr (fun l => regs_ok EE l RR) HRn16 sr' EQ : regs_ok EE sr' RR) as HRn16_; clear EQ HRn16; rename HRn16_ into HRn16 end.
  pose proof (W_sok_win C A10 m16 _ (s - 4096) (Z.to_nat 4096) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 1410112 m16 (canary_any m16)) as CANOK16.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m16]).
  pose proof (exW_kn_fixed SEGS C A10 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) (EVar 570) (EVar 32) (exW_canary SEGS 1410112 m16) s 4096 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  pose proof (mcs_canary_eq C A10 m16 _ CK HW16) as CEQ16.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  mh_drive 2000%nat 6000%nat STOPS2 (@nil bool) FDEF HK ST FZ.
  exb_exit ST Rc16 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A10 M16 (with_vmmaps vm10 md) /\ POSTM C A0 s m16 M16).
  { subst M16. apply (exW_win_blks C A10 A0 m16 _ E16 log16 (EVar 32) s 4096 [(EVar 68, sa, 24%Z); (EVar 102, arr, 400%Z); (EVar 170, s1, 6%Z); (EVar 204, s2, 7%Z)] CK HW16 SUB10 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a10 (conj Fsa F0sa))))|].
    constructor; [exact (conj eq_refl (conj RRarr (conj Larr_a10 (conj Farr F0arr))))|].
    constructor; [exact (conj eq_refl (conj RRs1 (conj Ls1_a10 (conj Fs1 F0s1))))|].
    constructor; [exact (conj eq_refl (conj RRs2 (conj Ls2_a10 (conj Fs2 F0s2))))|].
    constructor. }
  destruct WP16 as [HWs16 PMs16].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pixs); (68%nat, sa); (102%nat, arr); (136%nat, cstr); (170%nat, s1); (204%nat, s2); (304%nat, op1); (470%nat, op2)]).
  exW_regfactB BSF HR ex_r1 G1.
  exW_regfactB BSF HR ex_r2 G2.
  exW_regfactB BSF HR ex_r4 G4.
  exW_regfactB BSF HR ex_r10 G10.
  exW_regfactB BSF HR ex_r11 G11.
  exW_regfactB BSF HR ex_rg8 G8.
  exW_regfactB BSF HR ex_rg9 G9.
  exW_regfactB BSF HR ex_rg18 G18.
  exW_regfactB BSF HR ex_rg19 G19.
  exW_regfactB BSF HR ex_rg20 G20.
  exW_regfactW r0 HR ex_r3 G3.
  exW_cellB HK Hlf r0 BSF (EVar 68) sa 0%Z 4%nat Csa_0.
  exW_cellB HK Hlf r0 BSF (EVar 68) sa 4%Z 4%nat Csa_4.
  exW_cellB HK Hlf r0 BSF (EVar 68) sa 8%Z 4%nat Csa_8.
  exW_cellB HK Hlf r0 BSF (EVar 68) sa 16%Z 8%nat Csa_16.
  exW_cellB HK Hlf r0 BSF (EVar 102) arr 0%Z 8%nat Carr_0.
  exW_cellB HK Hlf r0 BSF (EVar 102) arr 8%Z 8%nat Carr_8.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 0%Z 1%nat Cs1_0.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 1%Z 1%nat Cs1_1.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 2%Z 1%nat Cs1_2.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 3%Z 1%nat Cs1_3.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 4%Z 1%nat Cs1_4.
  exW_cellB HK Hlf r0 BSF (EVar 170) s1 5%Z 1%nat Cs1_5.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 0%Z 1%nat Cs2_0.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 1%Z 1%nat Cs2_1.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 2%Z 1%nat Cs2_2.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 3%Z 1%nat Cs2_3.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 4%Z 1%nat Cs2_4.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 5%Z 1%nat Cs2_5.
  exW_cellB HK Hlf r0 BSF (EVar 204) s2 6%Z 1%nat Cs2_6.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-424)%Z 8%nat Cs_424.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-416)%Z 8%nat Cs_416.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-376)%Z 4%nat Cs_376.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-8)%Z 8%nat Cs_8.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-16)%Z 8%nat Cs_16.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-24)%Z 8%nat Cs_24.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-32)%Z 8%nat Cs_32.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-40)%Z 8%nat Cs_40.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-48)%Z 8%nat Cs_48.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-56)%Z 8%nat Cs_56.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-64)%Z 8%nat Cs_64.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-72)%Z 8%nat Cs_72.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-80)%Z 8%nat Cs_80.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-88)%Z 8%nat Cs_88.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-96)%Z 8%nat Cs_96.
  exW_cellB HK Hlf r0 BSF (EVar 32) s (-104)%Z 8%nat Cs_104.
  exact (HC A10 M16 vm10 Rc16 sa arr s1 s2
           HWs16 SUB10 (POSTM_trans _ _ _ _ _ _ PM16 PMs16) RM10 LDEL10 G1 G2 G3 G4 G10 G11 G8
           G9 G18 G19 G20 Lsa_a10 Fsa F0sa RRsa Larr_a10 Farr F0arr RRarr
           Ls1_a10 Fs1 F0s1 RRs1 Ls2_a10 Fs2 F0s2 RRs2 NE_sa_arr NE_sa_s1 NE_arr_s1 NE_sa_s2
           NE_arr_s2 NE_s1_s2 Csa_0 Csa_4 Csa_8 Csa_16 Carr_0 Carr_8 Cs1_0 Cs1_1 Cs1_2 Cs1_3
           Cs1_4 Cs1_5 Cs2_0 Cs2_1 Cs2_2 Cs2_3 Cs2_4 Cs2_5 Cs2_6 Cs_424 Cs_416 Cs_376
           Cs_8 Cs_16 Cs_24 Cs_32 Cs_40 Cs_48 Cs_56 Cs_64 Cs_72 Cs_80 Cs_88 Cs_96
           Cs_104
           ).
Qed.
End Chain.
