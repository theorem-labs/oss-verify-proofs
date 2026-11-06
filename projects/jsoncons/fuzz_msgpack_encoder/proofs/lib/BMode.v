(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
Class BMode : Type := mkBMode { bm_on : bool }.
Definition bm_off_inst : BMode := mkBMode false.
Definition bm_on_inst : BMode := mkBMode true.
#[global] Existing Instance bm_off_inst | 99.
(* [comment removed for export] *)
Class BmOff (bm : BMode) : Prop := bmoff_eq : @bm_on bm = false.
#[global] Instance bm_off_inst_off : BmOff bm_off_inst := @eq_refl bool false.
