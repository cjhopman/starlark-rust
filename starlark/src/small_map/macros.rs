macro_rules! def_iter {
    ($mapper:expr) => {
        fn next(&mut self) -> Option<Self::Item> {
            self.iter.next().map($mapper)
        }

        fn nth(&mut self, n: usize) -> Option<Self::Item> {
            self.iter.nth(n).map($mapper)
        }

        fn last(mut self) -> Option<Self::Item> {
            self.next_back()
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.iter.size_hint()
        }

        fn count(self) -> usize {
            self.iter.len()
        }



        fn collect<C>(self) -> C
            where C: std::iter::FromIterator<Self::Item>
        {
            self.iter.map($mapper).collect()
        }
    }
}
