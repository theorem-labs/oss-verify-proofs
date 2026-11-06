From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog Require Import SceneRunU.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.U.Prog.Seg Require Import SInv.
Import ListNotations.
Open Scope Z_scope.

Definition nG (g : ghost) : Z := nE (gbz (g_in g) 0) (gbz (g_in g) 1) (gbz (g_in g) 2).
Definition nbG (g : ghost) : Z := nbE (nG g).
Definition cG (g : ghost) : Z := cE (g_in g).
Definition stG (g : ghost) : Z := sx16 (gbz (g_in g) 3 + 256 * gbz (g_in g) 4).
Definition s7G (g : ghost) : Z := sx16 (256 * gbz (g_in g) 4).
Definition flG (g : ghost) : Z := gbz (g_in g) 0.

Definition macP (g : ghost) (m : word -> option byte) : Prop :=
  exists macb, length macb = 6%nat /\ bytes_at rsegs m (g_S g - 110) macb.

Definition bodyP (body len : Z) (m : word -> option byte) : Prop :=
  exists bb, Z.of_nat (length bb) = len /\ bytes_at rsegs m body bb.

Lemma gbz_range : forall d i, 0 <= gbz d i < 256.
Proof.
  intros d i. unfold gbz. destruct (nth_error d i) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. exact H.
Qed.

Lemma nG_range : forall g, 0 <= nG g <= 65535.
Proof.
  intros g. unfold nG, nE. pose proof (gbz_range (g_in g) 1). pose proof (gbz_range (g_in g) 2).
  destruct (Z.land _ 1 =? 0); lia.
Qed.

Lemma nbG_range : forall g, 1 <= nbG g <= 65535.
Proof.
  intros g. unfold nbG, nbE. pose proof (nG_range g). destruct (Z.eqb_spec (nG g) 0); lia.
Qed.

Section Cuts.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* Ubsan register map: n stays in s0 (x8) from the first malloc to the end; nb in s8 (x24); p + c in s5 (x21);
   st in s3 (x19); the input length left in s6 (x22); s7 (x23) = s7G; flags in s4 (x20). *)
Definition P15010 (g : ghost) (body : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = Z_to_bv 64 body /\ getr regs 8 = Z_to_bv 64 (nG g) /\ getr regs 24 = Z_to_bv 64 (nbG g) /\
  getr regs 21 = Z_to_bv 64 (g_p g + cG g) /\ getr regs 19 = Z_to_bv 64 (stG g) /\
  getr regs 22 = Z_to_bv 64 (g_n g - cG g) /\ getr regs 23 = Z_to_bv 64 (s7G g) /\
  getr regs 20 = Z_to_bv 64 (flG g) /\ macP g m.

Definition Inv_K15010 (g : ghost) (c : config) : Prop :=
  exists body, CUTST B APIf ra empty g 0x15010 1 [(body, nbG g)] (P15010 g body) c.

Definition Inv_K151b4 (g : ghost) (c : config) : Prop :=
  exists body again, CUTST B APIf ra empty g 0x151b4 2 [(body, nbG g); (again, 8904)] (fun regs m =>
    getr regs 10 = Z_to_bv 64 again /\ getr regs 9 = Z_to_bv 64 body /\ getr regs 8 = Z_to_bv 64 (nG g) /\
    nG g = 8904 /\ q64 m (fsp g + 16) 8904 /\ bodyP body 8904 m /\ macP g m) c.

Definition Inv_K15294 (g : ghost) (c : config) : Prop :=
  exists body, CUTST B APIf ra empty g 0x15294 2 [(body, nbG g)] (fun regs m =>
    getr regs 9 = Z_to_bv 64 body /\ getr regs 8 = Z_to_bv 64 (nG g) /\ nG g = 8904 /\
    q64 m (fsp g + 16) 8904 /\ bodyP body 8904 m /\ macP g m) c.

Definition Inv_K15298 (g : ghost) (c : config) : Prop :=
  exists body km, (km = 1 \/ km = 2) /\ CUTST B APIf ra empty g 0x15298 km [(body, nbG g)] (fun regs m =>
    getr regs 9 = Z_to_bv 64 body /\ getr regs 24 = Z_to_bv 64 (nbG g) /\ getr regs 8 = Z_to_bv 64 (nG g) /\
    bodyP body (nbG g) m /\ macP g m) c.

Definition Inv_K152a0 (g : ghost) (c : config) : Prop :=
  exists body before km, (km = 2 \/ km = 3) /\
    CUTST B APIf ra empty g 0x152a0 km [(body, nbG g); (before, nbG g)] (fun regs m =>
      getr regs 10 = Z_to_bv 64 before /\ getr regs 9 = Z_to_bv 64 body /\ getr regs 8 = Z_to_bv 64 (nG g) /\
      bodyP body (nbG g) m /\ macP g m) c.

Definition Inv_K15450 (g : ghost) (c : config) : Prop :=
  exists body km, CUTST B APIf ra empty g 0x15450 km [(body, nbG g)] (fun regs m =>
    getr regs 9 = Z_to_bv 64 body) c.

Definition Inv_K15458 (g : ghost) (c : config) : Prop :=
  exists km, CUTST B APIf ra empty g 0x15458 km [] (fun _ _ => True) c.

End Cuts.
