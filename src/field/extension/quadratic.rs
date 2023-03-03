
#[cfg(test)]
mod tests {
    mod bn128 {
        use crate::{test_field_arithmetic, test_field_extension};

        test_field_extension!(crate::field::bn128_base::Bn128Base, 2);
        test_field_arithmetic!(
            plonky2_field::extension::quadratic::QuadraticExtension<
                crate::field::bn128_base::Bn128Base,
            >
        );
    }
}
