(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits AXF_ff3.

Module AXF_tf.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_W := EVar 33.
Definition e_idx := EVar 34.
Definition e_p := EVar 35.
Definition e_avail := EVar 36.
Definition e_freed := EVar 37.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition e_sp0 := EVar 43.
Definition STK := SA e_sp0 (-1024).
Definition sr_tf := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-48)))) 8 (e_idx)) 9 (e_p)) 10 (e_G)) 11 (e_W)).
Definition kn_tf : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_p 5 (2^63-1);
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA (ELit 0) 0x95e63) 1 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWr (SA e_p (-3)) (ELit 3);
    KWr (SA e_G 28) (ELit 4);
    KDisj (SA e_G 24) (ELit 8) (SA e_p (-3)) (ELit 3);
    KDisj (SA (ELit 0) 0x95e63) (ELit 1) (SA e_p (-3)) (ELit 3);
    KDisj STK (ELit 1024) (SA e_p (-3)) (ELit 3);
    KDisj STK (ELit 1024) (SA e_G 24) (ELit 8) ].
Definition scr_tf : scripts := SCR [true; false; false] [] [].
Definition ss_tf := SS 0x516d0 sr_tf [] kn_tf 44.
Definition RUN_tf := sym_exec SEGS 200 true [] scr_tf ss_tf [].

Definition RES_tf := Eval vm_compute in RUN_tf.
Lemma RES_tf_ok : sym_exec SEGS 200 true [] scr_tf (SS 0x516d0 sr_tf [] kn_tf 44) [] = RES_tf.
Proof. vm_compute. reflexivity. Qed.
End AXF_tf.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_ff3 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_tfz.AXF_tf.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Record tail_pre (regs : bvmap 5 word) (m : word -> option byte) (G W idx p ra s0 s1 s2 s3 sp0 : Z) : Prop := {
  tp_R8 : getr regs 8 = wa idx ; tp_R9 : getr regs 9 = wa p ; tp_R10 : getr regs 10 = wa G ; tp_R11 : getr regs 11 = wa W ;
  tp_R2 : getr regs 2 = wa (sp0 - 48) ;
  tp_Rsp : 2^20 <= sp0 <= 2^47 ; tp_Asp : sp0 mod 16 = 0 ; tp_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  tp_RG : 1 <= G <= 2^63-1 ; tp_AG : G mod 8 = 0 ; tp_RW : 0 <= W <= 2^64-1 ; tp_Ridx : 0 <= idx <= 31 ; tp_Rp : 5 <= p <= 2^63-1 ;
  tp_Rra : 0 <= ra <= 2^64-1 ; tp_Rs0 : 0 <= s0 <= 2^64-1 ; tp_Rs1 : 0 <= s1 <= 2^64-1 ; tp_Rs2 : 0 <= s2 <= 2^64-1 ; tp_Rs3 : 0 <= s3 <= 2^64-1 ;
  tp_Mra : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  tp_Ms0 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  tp_Ms1 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  tp_Ms2 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  tp_Ms3 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  tp_Whdr : (forall d k, 0 <= d -> d + Z.of_nat k <= 3 -> store_ok SEGS m (wa (p + -3 + d)) k = true) ;
  tp_DSH : p + -3 + 3 <= sp0 + -1024 ;
  tp_DSG : G + 40 <= sp0 + -1024 ;
  tp_IH : p <= 0x10000 \/ 0x97000 <= p - 3 ;
  tp_IG : G + 40 <= 0x10000 \/ 0x97000 <= G ;
  tp_DHG : G + 40 <= p - 3 \/ p <= G
}.

Section TF.
Context {fx : FPState}.

Definition tf_mem (m : word -> option byte) (p G fnew : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m (wa (p - 3)) (word_to_le_bytes 1 (wa 255))) (wa (p - 2)) (word_to_le_bytes 2 (wa 0)))
    (wa (G + 28)) (word_to_le_bytes 4 (wa fnew)).

Definition tail_post (R regs : bvmap 5 word) (ra s0 s1 s2 s3 sp0 : Z) : Prop :=
  getr R 1 = wa ra /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ getr R 2 = wa sp0 /\
  (forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).

#[using="Type"] Theorem tf_arm : forall (regs : bvmap 5 word) (m rom : word -> option byte) (G W idx p avail freed ra s0 s1 s2 s3 sp0 : Z),
  tail_pre regs m G W idx p ra s0 s1 s2 s3 sp0 ->
  0 <= avail <= 2^32-1 -> 0 <= freed <= 2^32-1 ->
  rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ->
  rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ->
  rdn SEGS m (wa (0 + 613987)) 1 = Some (word_to_le_bytes 1 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 28 + d)) k = true) ->
  Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  freed <> 0 -> Z.lor avail freed + 2 ^ idx <> 2 ^ (Z.land W 31 + 1) - 1 ->
  exists R, msteps SEGS (mkst regs (wa 0x516d0) m rom) (mkst R (wa 0x517bc) (tf_mem m p G (freed + 2 ^ idx)) rom)
         /\ tail_post R regs ra s0 s1 s2 s3 sp0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G W idx p avail freed ra s0 s1 s2 s3 sp0 TP Rav Rfr Mav Mfr Mnl WG A2 A3 F1 F2.
  destruct TP as [R8 R9 R10 R11 R2 Rsp Asp HSTK RG AG RW Ridx Rp Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Whdr DSH DSG IH IG DHG].
  set (E := Env (reg_ev regs (fun n => wa (nth (n - 32) [G; W; idx; p; avail; freed; ra; s0; s1; s2; s3; sp0] 0))) (fun _ => [])).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = p) by exact (u_wa_small _ (rng64 _ _ _ Rp eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z43 : bv_unsigned (ev E 43) = sp0) by exact (u_wa_small _ (rng64 _ _ _ Rsp eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by exact (u_wa_small _ (rng64 _ _ _ Rra eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by exact (u_wa_small _ (rng64 _ _ _ Rs0 eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by exact (u_wa_small _ (rng64 _ _ _ Rs1 eq_refl)).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by exact (u_wa_small _ (rng64 _ _ _ Rs2 eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by exact (u_wa_small _ (rng64 _ _ _ Rs3 eq_refl)).
  assert (HR : regs_ok E sr_tf regs).
  { apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8);
      [apply (regs_ok_pin E sr_id regs 2); [apply regs_ok_id|] |] |] |] |].
    - rewrite R2, zeval_sound. cbn [zeval edenot e_sp0]. rewrite Z43. reflexivity.
    - rewrite R8. reflexivity.
    - rewrite R9. reflexivity.
    - rewrite R10. reflexivity.
    - rewrite R11. reflexivity. }
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (HK : know_ok SEGS E m kn_tf).
  { unfold know_ok, kn_tf.
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m e_sp0 (wa sp0) 1024); [reflexivity | exact HSTK | rewrite u_wa_small by (clear - Rsp; lia); clear - Rsp; lia])
               | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
    all: cbn [zeval edenot e_G e_W e_idx e_p e_avail e_freed e_ra e_s0 e_s1 e_s2 e_s3 e_sp0 STK a_base a_off].
    all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43.
    all: try zlit.
    all: try assumption.
    all: try zrange.
    all: try (intros d k Hd Hk; first [apply Whdr | apply WG]; assumption).
    all: try (left; assumption). all: try (right; assumption).
    all: try (rewrite ?(mod64_of_range _ _ _ RG eq_refl eq_refl), ?(mod64_of_range _ _ _ Rp eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rsp eq_refl eq_refl), ?(mod64_of_range _ _ _ Ridx eq_refl eq_refl),
                 ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl);
             first [assumption | (left; assumption) | (right; assumption)]).
    all: first [ (clear - DHG; lia) | (clear - IH; lia) | (clear - DSG; lia) ]. }
  assert (Hsc : scs_denot SEGS m E (snd (fst RES_tf))).
  { cbn [RES_tf fst snd].
    repeat (first [apply Forall_nil | apply Forall_cons]).
    all: apply sc_br_z; cbn [zeval edenot].
    all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z43.
    all: rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z.
    all: rewrite ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rav eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
    all: litmods.
    all: rewrite ?(Z.mod_small idx 32) by (clear - Ridx; lia).
    - rewrite (all_cond_z avail freed idx W Rav32 Rfr32 Ridx ltac:(clear - RW; lia) A2 A3). apply Z.eqb_neq. exact F2.
    - rewrite ext4_swrap, sx32_zero. apply Z.eqb_neq. rewrite (Z.mod_small freed _ Rfr32). exact F1.
    - rewrite !ext4_swrap, (mask2_bit_clear avail freed idx Rav32 Rfr32 Ridx A2 A3). reflexivity. }
  destruct (run_sound SEGS 200 [] scr_tf 0x516d0 sr_tf kn_tf 44 _ _ _ E m rom regs RES_tf_ok HR HK Hsc) as (R & HR' & _ & Hms). clear HK Hsc.
  exists R. split.
  - cbn [RES_tf fst snd s_pc s_log s_regs] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tf_mem m p G (freed + 2 ^ idx)) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot s_log]. unfold tf_mem.
    apply (f_equal3 wbytes); [ apply (f_equal3 wbytes); [ apply (f_equal3 wbytes); [ reflexivity | | ] | | reflexivity ] | | ].
    + rewrite adenot_z. cbn [zeval edenot]. rewrite Z35. f_equal; ring.
    + change (edenot E (ELit 18446744073709551615)) with (wa 18446744073709551615). apply le_wa_eqm; [reflexivity | apply Nat.leb_le; reflexivity].
    + rewrite adenot_z. cbn [zeval edenot]. rewrite Z35. f_equal; ring.
    + rewrite adenot_z. cbn [zeval edenot]. rewrite Z32. reflexivity.
    + rewrite zeval_sound. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. cbn [zeval edenot]. rewrite ?Z34, ?Z37.
      match goal with |- ?g => idtac g end.
      rewrite ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range _ _ _ Rfr eq_refl eq_refl).
      litmods. rewrite ?(Z.mod_small idx 32) by (clear - Ridx; lia). rewrite ?ext4_swrap.
      change (8 * Z.of_nat 4) with 32. rewrite swrap32_mod. rewrite Zplus_mod, swrap32_mod, swrap32_mod, <- Zplus_mod.
      rewrite Z.shiftl_1_l. reflexivity.
  - cbn [RES_tf fst snd s_regs] in HR'. clear Hms. unfold tail_post.
    Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.
    split; [srg HR'; reflexivity|]. split; [srg HR'; reflexivity|]. split; [srg HR'; reflexivity|].
    split; [srg HR'; reflexivity|]. split; [srg HR'; reflexivity|].
    split; [srg HR'; rewrite zeval_sound; f_equal; cbn [zeval edenot]; rewrite Z43; ring|].
    intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn]; [ rewrite (HR' _); reflexivity |]). destruct Hn.
Qed.
End TF.
