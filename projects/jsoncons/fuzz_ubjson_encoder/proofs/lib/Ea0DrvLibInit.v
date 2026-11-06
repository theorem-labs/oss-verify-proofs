(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg Hoare AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib
  HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface LibIfaceAB DrvKitA DrvNodesLazyK As0DrvKitA Ea0DrvEntry Ea0Drv_defs Ea0DrvLib Ea0DrvRead Ea0DrvStdio.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
Definition LIBINIT_KN : list kentry :=
  [KImg 65536 1286144; KImg 6766673 6766676; KImg 6766677 6773168; KImg 1300720 1300888; KImg 6905160 6905208;      (* [comment removed for export] *)
   KWord (SA (ELit 0) 6904512) 8 (EVar 3); KWord (SA (ELit 0) 6773176) 8 (ELit 6773176); KWord (SA (ELit 0) 6773208) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 6773360) 8 (EVar 3); KWord (SA (ELit 0) 6773328) 8 (ELit 6905160); KWord (SA (ELit 0) 6905112) 8 (EAlu ALU_ADD (EVar 1) (ELit (-160)));
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 6904528) 1 (ELit 0); KWord (SA (ELit 0) 6904532) 4 (ELit 0); KWord (SA (ELit 0) 6904536) 4 (ELit 2); KWord (SA (ELit 0) 6904544) 8 (ELit 6904552);
   KWord (SA (ELit 0) 6904552) 8 (ELit 0); KWord (SA (ELit 0) 6904560) 8 (ELit 1156008); KWord (SA (ELit 0) 6904816) 8 (ELit 622312);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 6904568) 8 (ELit 1156008); KWord (SA (ELit 0) 6904824) 8 (ELit 690352);
   KWord (SA (ELit 0) 6905107) 1 (ELit 0); KWord (SA (ELit 0) 6905328) 4 (ELit 0)].
(* [comment removed for export] *)
Definition LIBINIT_IMG : list (Z * Z) := [(65536, 1286144); (6766673, 6766676); (6766677, 6773168); (1300720, 1300888); (6905160, 6905208)].

(* [comment removed for export] *)
Definition INIT_CELLS_A : list (Z * Z * Z) :=
  [(6904528, 1, 0); (6904532, 4, 0); (6904536, 4, 2); (6904544, 8, 6904552); (6904552, 8, 0); (6904560, 8, 1156008); (6904816, 8, 622312);
   (6905107, 1, 0); (6905328, 4, 0); (6904568, 8, 1156008); (6904824, 8, 690352)].

(* [comment removed for export] *)
Record drv_lib_cellsA (Lay : lib_layoutA) : Prop := DRV_LIB_CELLSA {
  dlc_td_self : lla_td_self Lay = 0x6759b8;  dlc_td_tid : lla_td_tid Lay = 0x6759d8;  dlc_td_canary : lla_td_canary Lay = 0x675a70;
  dlc_td_locale : lla_td_locale Lay = 0x675a50;  dlc_locale : lla_locale Lay = 0x695d48;  dlc_guard : lla_guard Lay = 0x695ac0;
  dlc_auxvp : lla_auxvp Lay = 0x695d18;  dlc_phdr : lla_phdr Lay = 0x10040;  dlc_phent : lla_phent Lay = 56;  dlc_phnum : lla_phnum Lay = 11;
  dlc_init_img : forall iv, In iv (lla_init_img Lay) -> exists lo hi, In (lo, hi) LIBINIT_IMG /\ lo <= fst iv /\ snd iv <= hi;
  (* [comment removed for export] *)
  dlc_rw_lo : lla_rw_lo Lay <= 0x13dab0;
  dlc_initc : forall iv, In iv (lla_initc Lay) -> 0 <= fst iv /\ snd iv <= 0x698000 /\ (snd iv <= 0x13dab0 \/ 0x13db98 <= fst iv) /\ (snd iv <= 0x6962a0 \/ 0x6966a0 <= fst iv)
                                                /\ (snd iv <= 0x674054 \/ 0x674055 <= fst iv);
  (* [comment removed for export] *)
  dlc_init_cells : lla_init_cells Lay = INIT_CELLS_A
}.

Lemma locale_imgA : forall k, (k < 6)%nat ->
  rdn ASEGS (fun _ => None) (Z_to_bv 64 (0x695d48 + 8 * Z.of_nat k)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros k Hk. do 6 (destruct k as [|k]; [vm_compute; reflexivity|]). lia. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section LibInit.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable M0 : word -> option byte.
  Variable Lay : lib_layoutA.
  Hypothesis LayL : lla_L Lay = L.
  Hypothesis DLC : drv_lib_cellsA Lay.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).

  Theorem lib_init_at_call : forall vals ebs kn LB LK cr A M (model : Model) (p0 : word),
    know_ok ASEGS (Env (vals_ev vals) ebs) (mrestrict (ahid A model) M) kn ->
    forallb (fun K => existsb (kentry_eqb K) kn) LIBINIT_KN = true ->
    vals_ev vals 1 = p0 ->
    dinvA LB LK cr A M model -> auxv_atA sp0 p0 M0 ->
    exists av uid rnd tid canary hw, lib_init_factsA Lay ar av uid rnd tid canary hw M.
Proof. intros vals ebs kn LB LK cr A M model p0.
intros HK HB P1 D (uidz & rnd & hwz & AW & AU & AH & AR1 & AR2 & AP & AP8).
pose proof Hsp as Hsp'. set (E := Env (vals_ev vals) ebs) in *. set (MV := mrestrict (ahid A model) M) in *.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as (HOFF & _).
rewrite forallb_forall in HB.
assert (KB : forall K, In K LIBINIT_KN -> existsb (kentry_eqb K) kn = true) by (intros K HKin; exact (HB K HKin)).
assert (FULLR : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M (Z_to_bv 64 a) n = Some bs)
by (intros a n bs Hr; exact (rdn_of_mrestrict ASEGS _ M HOFF n _ bs Hr)).
assert (NONE : forall lo hi, In (KImg lo hi) LIBINIT_KN -> hi <= 0x698000 -> forall i, 0 <= lo -> lo <= i < hi -> M (Z_to_bv 64 i) = None).
{ intros lo hi Hin Hhi i Hlo Hi. pose proof (kimg_clear E MV kn lo hi HK (KB _ Hin) i Hi) as X. unfold MV, mrestrict in X.
rewrite (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ i D ltac:(lia)) in X. exact X. }
assert (KW : forall a (w : nat) v, In (KWord (SA (ELit 0) a) w v) LIBINIT_KN -> 0 <= a -> a + Z.of_nat w <= 2 ^ 63 ->
rdn ASEGS M (Z_to_bv 64 a) w = Some (word_to_le_bytes w (edenot E v))).
{ intros a w v Hin Ha Hw. apply FULLR. exact (kword_lit sp0 E MV kn a w v HK (KB _ Hin) Ha Hw). }
pose proof (KW 6904512 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CG.
pose proof (KW 6773176 8%nat (ELit 6773176) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CS.
pose proof (KW 6773208 4%nat (EVar 4) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CT.
pose proof (KW 6773360 8%nat (EVar 3) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CC.
pose proof (KW 6773328 8%nat (ELit 6905160) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CL.
pose proof (KW 6905112 8%nat (EAlu ALU_ADD (EVar 1) (ELit (-160))) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as CA.
assert (TR : 1 <= bv_unsigned (vals_ev vals 4) <= 4194303).
{ pose proof (KB (KRange (EVar 4) 1 4194303) ltac:(unfold LIBINIT_KN; cbn [In]; tauto)) as Hb.
apply existsb_exists in Hb as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
pose proof (proj1 (Forall_forall _ _) HK _ Hin) as X. cbn [kentry_ok edenot ev E] in X. exact X. }
cbn [edenot ev E] in CG, CS, CT, CC, CL, CA. rewrite P1 in CA.
assert (EA : alu64 ALU_ADD p0 (Z_to_bv 64 (-160)) = Z_to_bv 64 (bv_unsigned p0 - 160)).
{ rewrite alu_add. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. }
rewrite EA in CA.
set (av := bv_unsigned p0 - 160) in *.
exists av, uidz, rnd, (bv_unsigned (vals_ev vals 4)), (bv_unsigned (vals_ev vals 3)), hwz.
destruct DLC as [d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 dimg _ _ dcells].
assert (CELLS : Forall (fun c => cellz ASEGS M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) INIT_CELLS_A).
{ unfold INIT_CELLS_A.
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904528 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904532 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904536 4%nat (ELit 2) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904544 8%nat (ELit 6904552) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904552 8%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904560 8%nat (ELit 1156008) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904816 8%nat (ELit 622312) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6905107 1%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6905328 4%nat (ELit 0) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904568 8%nat (ELit 1156008) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_cons; [cbn [fst snd]; unfold cellz; exact (KW 6904824 8%nat (ELit 690352) ltac:(unfold LIBINIT_KN; cbn [In]; tauto) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))|].
apply Forall_nil. }
unfold lib_init_factsA. split.
2:{ rewrite dcells, LayL, (dla_segs _ _ _ _ DL). exact CELLS. }
unfold lib_init_facts. cbn [lib_view ll_heap heap_view HeapIface.hl_segs hl_sptop ll_init_img ll_td_self ll_td_tid ll_td_locale ll_locale ll_td_canary ll_guard ll_auxvp].
rewrite LayL, (dla_segs _ _ _ _ DL), (dla_sptop _ _ _ _ DL), d1, d2, d3, d4, d5, d6, d7. unfold cellz.
rewrite !Z_to_bv_bv_unsigned.
split. { intros iv a Hiv Ha. destruct (dimg iv Hiv) as (lo & hi & Hin & H1 & H2).
unfold LIBINIT_IMG in Hin. cbn [In] in Hin.
destruct Hin as [X|[X|[X|[X|[X|[]]]]]]; injection X as <- <-;
[apply (NONE 65536 1286144) | apply (NONE 6766673 6766676) | apply (NONE 6766677 6773168) | apply (NONE 1300720 1300888) | apply (NONE 6905160 6905208)];
first [lia | (unfold LIBINIT_KN; cbn [In]; tauto)]. }
split; [exact CS|]. split; [exact CT|]. split; [lia|]. split; [exact CL|].
split. { intros k Hk. apply (img_cell M _ 8%nat _ (locale_imgA k Hk)); [lia | cbn; lia|].
intros i Hi. apply (NONE 6905160 6905208); [unfold LIBINIT_KN; cbn [In]; tauto | lia | lia | cbn in Hi; lia]. }
split; [exact CC|]. split; [exact CG|]. split; [pose proof (bv_unsigned_in_range _ (vals_ev vals 3)) as X; change (bv_modulus 64) with (2 ^ 64) in X; lia|].
split; [exact CA|]. split; [unfold av; lia|]. split; [unfold av; lia|].
split. { unfold av. rewrite <- Zminus_mod_idemp_l, AP8. reflexivity. }
split. { intros j Hj. unfold auxv_words. cbn [lib_view ll_phdr ll_phent ll_phnum]. rewrite d8, d9, d10.
apply (rdn_tr M0 M _ 8%nat _ (AW j Hj)); [unfold av; lia | unfold av; cbn; lia|].
intros i Hi. apply (di_above _ _ _ _ _ _ _ _ _ _ D). unfold av in *. cbn in Hi. lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
apply Forall_forall. cbn [lib_view ll_init_cells]. intros c Hc. destruct Hc.
Qed.
End LibInit.
End FPX_1.
